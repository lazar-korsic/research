import Kritzinger.Dyadic
import Mathlib.Data.Nat.Log
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

namespace Kritzinger
open Finset MeasureTheory
open scoped ENNReal
noncomputable section

theorem close_to_mean {x : Seq} {s N : ℕ} (g : GreedyFrom x s) 
    (hN : 0 < N) {a t b : ℝ} (ht : t ∈ Set.Ioc a b)
    (hshort : b-a ≤ 1/(2*(N:ℝ))) :
    |D x N t - S x N a b| ≤ (s:ℝ)+2 := by
  classical
  have hab := ht.1.trans_le ht.2
  have hp := sub_pos.mpr hab
  let inside := (range N).filter (fun i => a<x i ∧ x i<b)
  let late := inside.filter (fun i => s ≤ i)
  have hsN : (0:ℝ) < N := by exact_mod_cast hN
  have hcard : late.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    have aux (i j : ℕ) (hi : i ∈ late) (hj : j ∈ late) (hij : i < j) : False := by
      have hiI := (mem_filter.mp hi).1
      have hai := (mem_filter.mp hiI).2.1
      have hib := (mem_filter.mp hiI).2.2
      obtain ⟨hjI,hjs⟩ := mem_filter.mp hj
      obtain ⟨hjN,haj,hjb⟩ := mem_filter.mp hjI
      have hh := separation_step (g.2 j hjs) hij
      have hC : (j:ℝ)+1 ≤ N := by exact_mod_cast (show j+1 ≤ N by have := mem_range.mp hjN; omega)
      have h' : 1/(2*(N:ℝ)) ≤ 1/(2*((j:ℝ)+1)) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have hx : |x j-x i| < b-a := abs_lt.mpr ⟨by linarith,by linarith⟩
      linarith [h'.trans hh]
    rcases lt_trichotomy i j with h | h | h
    · exact (aux i j hi hj h).elim
    · exact h
    · exact (aux j i hj hi h).elim
  have hall : inside.card ≤ s+1 := by
    have h : inside ⊆ range s ∪ late := by
      intro i hi
      by_cases h : i < s
      · exact mem_union_left _ (mem_range.mpr h)
      · exact mem_union_right _ (mem_filter.mpr ⟨hi,le_of_not_gt h⟩)
    exact (card_le_card h).trans ((card_union_le _ _).trans (by simp; omega))
  let z (i : ℕ) := (if x i<t then (1:ℝ) else 0) -
      (max 0 (b-x i)-max 0 (a-x i))/(b-a)
  have he : D x N t - S x N a b =
      (∑ i ∈ range N, z i) + (N:ℝ)*((a+b)/2-t) := by
    unfold D S H z
    rw [sum_sub_distrib, ← sum_div, sum_sub_distrib]
    field_simp
    ring
  have hz (i : ℕ) (hi : i ∈ range N) : |z i| ≤ if i ∈ inside then 1 else 0 := by
    dsimp [z]
    by_cases h : a<x i ∧ x i<b
    · rw [if_pos (mem_filter.mpr ⟨hi,h⟩), max_eq_left (by linarith : a-x i ≤ 0),
        max_eq_right (by linarith : 0 ≤ b-x i), sub_zero]
      have h0 := div_nonneg (sub_nonneg.mpr h.2.le) hp.le
      have h1 := (div_le_one hp).2 (show b-x i ≤ b-a by linarith [h.1])
      apply abs_le.mpr
      split_ifs <;> constructor <;> linarith
    · rw [if_neg (show i ∉ inside from fun hm => h (mem_filter.mp hm).2)]
      by_cases h' : x i ≤ a
      · rw [if_pos (h'.trans_lt ht.1), max_eq_right (by linarith : 0 ≤ b-x i),
          max_eq_right (sub_nonneg.mpr h'),
          show b-x i-(a-x i)=b-a by ring, div_self hp.ne', sub_self, abs_zero]
      · have h'' : b ≤ x i := le_of_not_gt (fun h'' => h ⟨lt_of_not_ge h',h''⟩)
        rw [if_neg (not_lt.mpr (ht.2.trans h'')), max_eq_left (sub_nonpos.mpr h''),
          max_eq_left (sub_nonpos.mpr (hab.le.trans h'')), sub_self, zero_div, sub_self, abs_zero]
  have hz' : |∑ i ∈ range N, z i| ≤ (s:ℝ)+1 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans ((sum_le_sum hz).trans _)
    simp only [sum_ite, sum_const, Finset.sum_const_zero, nsmul_eq_mul, mul_one, add_zero]
    have hfilter : (range N).filter (fun i => i ∈ inside) = inside :=
      by
        ext i
        simp only [mem_filter, inside]
        tauto
    rw [hfilter]
    exact_mod_cast hall
  have ht' : |(a+b)/2-t| ≤ b-a := abs_le.mpr ⟨by linarith [ht.1,ht.2],by linarith [ht.1,ht.2]⟩
  have hm := mul_le_mul_of_nonneg_left (ht'.trans hshort) hsN.le
  have e : (N:ℝ)*(1/(2*(N:ℝ)))=1/2 := by
    field_simp [hsN.ne']; ring
  rw [e] at hm
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_of_pos hsN]
  linarith


theorem measurable_D (x : Seq) (n : ℕ) : Measurable (D x n) := by
  unfold D
  apply Measurable.sub _ (measurable_const.mul measurable_id)
  exact Finset.measurable_sum _ (fun i _ => measurable_const.indicator measurableSet_Ioi)

theorem interval_integrable_power (x : Seq) (n d : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    IntervalIntegrable (fun t => |D x n t|^d) volume a b := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hab]
  apply Measure.integrableOn_of_bounded (M := (n:ℝ)^d) (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    ((continuous_abs.measurable.comp (measurable_D x n)).pow_const _).aestronglyMeasurable
  rw [ae_restrict_iff' measurableSet_Ioc]
  exact ae_of_all _ fun t ht => by
    change ‖|D x n t|^d‖ ≤ (n:ℝ)^d
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg (D x n t)) d)]
    exact pow_le_pow_left₀ (abs_nonneg _) (D_seed x n ⟨ha.trans ht.1.le,ht.2.trans hb⟩) _

theorem fine_grid_integral {x : Seq} {s n r j : ℕ} (g : GreedyFrom x s)
    (hn : 0 < n) (hmesh : 2*n ≤ 2^j) :
    (∫ t in (0:ℝ)..1, |D x n t|^(2*r)) ≤
    (∑ i ∈ range (2^j), (2*((cellMean x n (2^j) i)^2+((s:ℝ)+2)^2))^r)/((2^j:ℕ):ℝ) := by
  let M : ℕ := 2^j
  let a (i : ℕ) : ℝ := (i:ℝ)/M
  let f (t : ℝ) := |D x n t|^(2*r)
  have hm : (0:ℝ) < M := by exact_mod_cast (show 0 < M by dsimp [M]; positivity)
  have hN : (0:ℝ) < n := by exact_mod_cast hn
  have a0 : a 0 = 0 := by simp [a]
  have aM : a M = 1 := by simp [a,hm.ne']
  have ha (i : ℕ) : 0 ≤ a i := by dsimp [a]; positivity
  have hb (i : ℕ) (hi : i < M) : a (i+1) ≤ 1 := by
    dsimp [a]; exact (div_le_one hm).2 (by exact_mod_cast Nat.succ_le_of_lt hi)
  have hlt (i : ℕ) : a i < a (i+1) := by
    dsimp [a]; exact div_lt_div_of_pos_right (by exact_mod_cast Nat.lt_succ_self i) hm
  change (∫ t in (0:ℝ)..1, f t) ≤ _
  rw [← a0, ← aM, ← intervalIntegral.sum_integral_adjacent_intervals
    (fun k hk => interval_integrable_power x n (2*r) (ha k) (hlt k).le (hb k hk))]
  change _ ≤ (∑ i ∈ range M, _)/(M:ℝ)
  rw [sum_div]
  apply sum_le_sum
  intro i hi
  let z := cellMean x n M i
  let E : ℝ := (s:ℝ)+2
  let B : ℝ := (2*(z^2+E^2))^r
  have hlen : a (i+1)-a i = 1/(M:ℝ) := by
    dsimp [a]; push_cast; ring
  have hshort : a (i+1)-a i ≤ 1/(2*(n:ℝ)) := by
    rw [hlen]
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast hmesh
  have hh := intervalIntegral.integral_mono_on_of_le_Ioo (hlt i).le
    (interval_integrable_power x n (2*r) (ha i) (hlt i).le (hb i (mem_range.mp hi)))
    (show IntervalIntegrable (fun _ : ℝ => B) volume (a i) (a (i+1)) from intervalIntegrable_const)
    (fun t ht => by
      have h := close_to_mean g hn ⟨ht.1,ht.2.le⟩ hshort
      have hz : S x n (a i) (a (i+1)) = z := by simp [a,z,cellMean,Nat.cast_add]
      rw [hz] at h
      change |D x n t-z| ≤ E at h
      have h1 := (abs_le.1 h).1
      have h2 := (abs_le.1 h).2
      have h3 := mul_nonneg (show 0 ≤ E-(D x n t-z) by linarith)
        (show 0 ≤ E+(D x n t-z) by linarith)
      have h4 : (D x n t)^2 ≤ 2*(z^2+E^2) := by nlinarith only [h3,sq_nonneg (D x n t-2*z)]
      dsimp [f,B]
      rw [pow_mul, sq_abs]
      exact pow_le_pow_left₀ (sq_nonneg _) h4 r)
  rw [intervalIntegral.integral_const, hlen, smul_eq_mul] at hh
  change (∫ u in a i..a (i+1), f u) ≤ B/(M:ℝ)
  simpa only [one_div,one_mul,mul_comm B,div_eq_mul_inv] using hh

theorem dyadic_energy_bound (s r : ℕ) (hr : 0 < r) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ x n, GreedyFrom x s → s ≤ n → ∀ j,
      dyadicEnergy x n j r ≤ (seedBound s)^2+(j:ℝ)*U := by
  obtain ⟨V,hV,hrow⟩ := cell_row_moment s (2*r)
  let U : ℝ := (2:ℝ)^(2*r)*(2*V)^(1/(r:ℝ))
  refine ⟨U,by dsimp [U]; positivity,?_⟩
  intro x n g hs j
  induction j with
  | zero =>
    have h₁ := boundary_from g hs (show (1:ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    have h₂ := boundary_from (reflect_from g) hs (show (1:ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    rw [H_reflect_of_unit g.1,sub_self,H_zero_of_unit g.1,zero_sub,mul_one] at h₂
    have hr' : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    simp only [dyadicEnergy,powerMean,pow_zero,sum_range_one,Nat.cast_one,div_one,
      cellMean,Nat.cast_zero,zero_add,S,H_zero_of_unit g.1,sub_zero, Nat.cast_zero,zero_mul,add_zero]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (sq_nonneg _),mul_one_div_cancel hr',Real.rpow_one]
    have hab : |H x n 1| ≤ seedBound s := abs_le.mpr ⟨by linarith,by linarith⟩
    simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hab 2
  | succ j ih =>
    have hh := dyadic_step hr V (fun M hM => hrow x n M g hs hM) j
    change _ ≤ _ + U at hh
    rw [Nat.cast_succ]
    linarith


theorem powerMean_const {m r : ℕ} (hm : 0 < m) (hr : 0 < r) {c : ℝ} (hc : 0 ≤ c) :
    powerMean m r (fun _ => c) = c := by
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hr' : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  unfold powerMean
  rw [sum_const,nsmul_eq_mul,card_range,mul_comm, mul_div_cancel_right₀ _ hm',
    ← Real.rpow_natCast, ← Real.rpow_mul hc,mul_one_div_cancel hr',Real.rpow_one]

theorem log_mesh (n : ℕ) (hn : 0 < n) :
    (Nat.clog 2 (2*n):ℝ) ≤ 1+Real.log (2*(n:ℝ))/Real.log 2 := by
  let j := Nat.clog 2 (2*n)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  rcases Nat.eq_zero_or_pos j with hj | hj
  · change (j:ℝ) ≤ _
    rw [hj,Nat.cast_zero]
    linarith [div_nonneg (Real.log_nonneg (show 1 ≤ 2*(n:ℝ) by linarith)) hlog.le]
  have h := (Nat.pow_lt_iff_lt_clog (by norm_num : 1 < (2:ℕ))).2
    (show j-1 < Nat.clog 2 (2*n) by change j-1<j; omega)
  have h' : (2:ℝ)^(j-1) < 2*(n:ℝ) := by exact_mod_cast h
  have h'' := Real.log_le_log (show 0 < (2:ℝ)^(j-1) by positivity) h'.le
  rw [Real.log_pow, Nat.cast_sub (by omega), Nat.cast_one] at h''
  change (j:ℝ) ≤ _
  have hdiv := (le_div_iff₀ hlog).2 h''
  linarith

def unitMeasure : Measure ℝ := volume.restrict (Set.Ioc 0 1)

instance : IsProbabilityMeasure unitMeasure :=
  ⟨by simp [unitMeasure, Measure.restrict_apply_univ, Real.volume_Ioc]⟩

theorem even_norm_eq {x : Seq} (n r : ℕ) (hr : 0 < r) :
    eLpNorm (D x n) (2*r:ℕ) unitMeasure =
      ENNReal.ofReal (Real.sqrt (((∫ t in (0:ℝ)..1, |D x n t|^(2*r)))^(1/(r:ℝ)))) := by
  have hq : (2*r:ℕ) ≠ 0 := by omega
  have hp : (0:ℝ) < r := by exact_mod_cast hr
  have hpos : 0 ≤ ∫ t in (0:ℝ)..1, |D x n t|^(2*r) :=
    intervalIntegral.integral_nonneg (by norm_num) (fun t _ => by positivity)
  rw [eLpNorm_eq_lintegral_rpow_enorm (by exact_mod_cast hq) (ENNReal.natCast_ne_top _),
    ENNReal.toReal_natCast]
  simp_rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (abs_nonneg _)]
  have h := ofReal_integral_eq_lintegral_ofReal
    (interval_integrable_power x n (2*r) (by norm_num : (0:ℝ) ≤ 0)
      (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) ≤ 1)).1
    (ae_of_all unitMeasure fun t => pow_nonneg (abs_nonneg (D x n t)) _)
  rw [unitMeasure, ← h, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hpos,
    ENNReal.ofReal_rpow_of_nonneg hpos (by positivity)]
  push_cast
  rw [show (1:ℝ)/(2*(r:ℝ)) = 1/(r:ℝ)*(1/2) by ring]

/-- Finite Lᵖ discrepancy on the unit interval, uniformly over the initial
    configuration of the given length and over all choices of greedy ties. -/
theorem finite_Lp_from_seed (s : ℕ) (p : ℝ≥0∞) (hp : p < ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Seq) (n : ℕ), GreedyFrom x s → s ≤ n → 0 < n →
      eLpNorm (D x n) p unitMeasure ≤
        ENNReal.ofReal (C*Real.sqrt (Real.log (2*(n:ℝ)))) := by
  obtain ⟨r,hr⟩ := exists_nat_gt p.toReal
  have hR : 0 < r := by
    by_contra! hh
    have e : r=0 := by omega
    simp [e,not_lt.mpr ENNReal.toReal_nonneg] at hr
  have he : p ≤ (2*r:ℕ) := by
    apply (ENNReal.toReal_le_toReal hp.ne (ENNReal.natCast_ne_top _)).mp
    rw [ENNReal.toReal_natCast]
    push_cast
    linarith [ENNReal.toReal_nonneg (a := p)]
  obtain ⟨U,hU,hdy⟩ := dyadic_energy_bound s r hR
  let E : ℝ := (s:ℝ)+2
  let C0 : ℝ := 2*((seedBound s)^2+2*U+E^2)/Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  refine ⟨Real.sqrt C0, Real.sqrt_nonneg _, ?_⟩
  intro x n g hs hn
  let j := Nat.clog 2 (2*n)
  let m : ℕ := 2^j
  have hm : 0 < m := by dsimp [m]; positivity
  have hmesh : 2*n ≤ 2^j := Nat.le_pow_clog (by norm_num : 1 < (2:ℕ)) (2*n)
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlg : Real.log 2 ≤ Real.log (2*(n:ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlg0 : 0 ≤ Real.log (2*(n:ℝ)) := hlog2.le.trans hlg
  have h1 := fine_grid_integral (r := r) g hn hmesh
  have hV : 0 ≤ ∫ t in (0:ℝ)..1, |D x n t|^(2*r) :=
    intervalIntegral.integral_nonneg (by norm_num) (fun t _ => by positivity)
  have h2 := Real.rpow_le_rpow hV h1 (show 0 ≤ 1/(r:ℝ) by positivity)
  change _ ≤ powerMean m r (fun i => 2*((cellMean x n m i)^2+E^2)) at h2
  rw [powerMean_smul m hR (by norm_num : (0:ℝ) ≤ 2)] at h2
  swap
  · intro i; positivity
  have hadd := powerMean_add m hR (fun i => (cellMean x n m i)^2) (fun _ => E^2)
    (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
  rw [powerMean_const hm hR (sq_nonneg E)] at hadd
  have hdy' := hdy x n g hs j
  change powerMean m r (fun i => (cellMean x n m i)^2) ≤ _ at hdy'
  have hmesh' := log_mesh n hn
  change (j:ℝ) ≤ _ at hmesh'
  have hratio : 1 ≤ Real.log (2*(n:ℝ))/Real.log 2 :=
    (le_div_iff₀ hlog2).2 (by simpa using hlg)
  have hjU := mul_le_mul_of_nonneg_right hmesh' hU
  have hratio' := mul_le_mul_of_nonneg_right hratio
    (show 0 ≤ (seedBound s)^2+U+E^2 by positivity)
  have hfinal : (∫ t in (0:ℝ)..1, |D x n t|^(2*r))^(1/(r:ℝ)) ≤
      C0*Real.log (2*(n:ℝ)) := by
    have h3 := mul_le_mul_of_nonneg_left hadd (by norm_num : (0:ℝ) ≤ 2)
    have e : C0*Real.log (2*(n:ℝ)) =
        2*((seedBound s)^2+2*U+E^2)*(Real.log (2*(n:ℝ))/Real.log 2) := by dsimp [C0]; ring
    rw [e]
    apply (h2.trans h3).trans
    have h4 := mul_le_mul_of_nonneg_left
      (add_le_add_right hdy' (E^2)) (show (0:ℝ) ≤ 2 by norm_num)
    apply h4.trans
    nlinarith only [hjU,hratio']
  have hnorm := eLpNorm_le_eLpNorm_of_exponent_le (μ := unitMeasure) he
    (measurable_D x n).aestronglyMeasurable
  rw [even_norm_eq n r hR] at hnorm
  apply hnorm.trans
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.sqrt_mul hC0]
  exact Real.sqrt_le_sqrt hfinal

theorem finite_Lp (p : ℝ≥0∞) (hp : p < ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Seq) (n : ℕ), Greedy x → 0 < n →
      eLpNorm (D x n) p unitMeasure ≤ ENNReal.ofReal (C*Real.sqrt (Real.log (2*(n:ℝ)))) := by
  obtain ⟨C,hC,h⟩ := finite_Lp_from_seed 0 p hp
  exact ⟨C,hC,fun x n g hn => h x n ⟨g.1,fun j _ => g.2 j⟩ (Nat.zero_le _) hn⟩

#print axioms finite_Lp_from_seed
#print axioms finite_Lp
end
end Kritzinger
