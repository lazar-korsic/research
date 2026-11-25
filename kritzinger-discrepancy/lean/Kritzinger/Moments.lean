import Kritzinger.Seeded
import Mathlib.Analysis.SpecificLimits.Normed

namespace Kritzinger
open Finset MeasureTheory
noncomputable section

/-- Difference between an interval mean and the mean on its left part. -/
theorem chord_left (x : Seq) (n : ℕ) {a t b : ℝ} (hat : a < t) (htb : t < b) :
    S x n a b - S x n a t = chord x n a t b / (t-a) := by
  unfold S chord
  field_simp [(sub_pos.mpr hat).ne', (sub_pos.mpr (hat.trans htb)).ne']
  ring

/-- Difference between the mean on the right part and the full mean. -/
theorem chord_right (x : Seq) (n : ℕ) {a t b : ℝ} (hat : a < t) (htb : t < b) :
    S x n t b - S x n a b = chord x n a t b / (b-t) := by
  unfold S chord
  field_simp [(sub_pos.mpr htb).ne', (sub_pos.mpr (hat.trans htb)).ne']
  ring

theorem mean_extend_right {x : Seq} {s n : ℕ} (g : GreedyFrom x s) (hs : s ≤ n)
    {a t b : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1)
    (hat : a < t) (htb : t ≤ b) (hlen : b-t ≤ t-a) :
    S x n a b - S x n a t ≤ (s:ℝ)+1 := by
  rcases htb.eq_or_lt with h | h
  · rw [h, sub_self]
    positivity
  rw [chord_left x n hat h]
  apply (div_le_iff₀ (sub_pos.mpr hat)).2
  have h₁ := chord_from_seed g hs ha hb hat h
  have h₂ := Real.sqrt_le_sqrt hlen
  have h₃ := mul_le_mul_of_nonneg_left h₂ (Real.sqrt_nonneg (t-a))
  rw [← pow_two, Real.sq_sqrt (sub_nonneg.mpr hat.le)] at h₃
  exact h₁.trans (mul_le_mul_of_nonneg_left h₃ (by positivity))

theorem mean_extend_left {x : Seq} {s n : ℕ} (g : GreedyFrom x s) (hs : s ≤ n)
    {a t b : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1)
    (hat : a ≤ t) (htb : t < b) (hlen : t-a ≤ b-t) :
    S x n t b - S x n a b ≤ (s:ℝ)+1 := by
  rcases hat.eq_or_lt with h | h
  · rw [h, sub_self]
    positivity
  rw [chord_right x n h htb]
  apply (div_le_iff₀ (sub_pos.mpr htb)).2
  have h₁ := chord_from_seed g hs ha hb h htb
  have h₂ := Real.sqrt_le_sqrt hlen
  have h₃ := mul_le_mul_of_nonneg_right h₂ (Real.sqrt_nonneg (b-t))
  rw [← pow_two, Real.sq_sqrt (sub_nonneg.mpr htb.le)] at h₃
  exact h₁.trans (mul_le_mul_of_nonneg_left h₃ (by positivity))

theorem mean_extend_right_pow {x : Seq} {s n : ℕ} (g : GreedyFrom x s) (hs : s ≤ n)
    (k : ℕ) {a t b : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1)
    (hat : a < t) (htb : t ≤ b) (hlen : b-a ≤ (2:ℝ)^k*(t-a)) :
    S x n a b - S x n a t ≤ (k:ℝ)*((s:ℝ)+1) := by
  induction k generalizing b with
  | zero =>
      have he : b = t := by simp at hlen; linarith
      simp [he]
  | succ k ih =>
      let c := min b (a+(2:ℝ)^k*(t-a))
      have ht' : t ≤ c := by
        apply le_min htb
        have hh : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
        nlinarith [mul_le_mul_of_nonneg_right hh (sub_nonneg.mpr hat.le)]
      have hcb : c ≤ b := min_le_left _ _
      have hc : c ∈ Set.Icc (0:ℝ) 1 :=
        ⟨ha.1.trans (hat.le.trans ht'), hcb.trans hb.2⟩
      have hc1 : c-a ≤ (2:ℝ)^k*(t-a) := by
        have h : c ≤ a+(2:ℝ)^k*(t-a) := min_le_right _ _
        linarith
      have hc2 : b-c ≤ c-a := by
        dsimp [c]
        rcases le_total b (a+(2:ℝ)^k*(t-a)) with h | h
        · rw [min_eq_left h]; linarith
        · rw [min_eq_right h, pow_succ] at *
          linarith
      have e1 := ih hc ht' hc1
      have e2 := mean_extend_right g hs ha hb (hat.trans_le ht') hcb hc2
      push_cast
      nlinarith


theorem S_reflect {x : Seq} (hx : ∀ i, x i ∈ Set.Icc (0:ℝ) 1)
    (n : ℕ) (a b : ℝ) : S (reflect x) n a b = -S x n (1-b) (1-a) := by
  unfold S
  rw [H_reflect_of_unit hx, H_reflect_of_unit hx]
  rw [show (1-a)-(1-b)=b-a by ring, ← neg_div]
  congr 1
  ring

theorem mean_extend_left_pow {x : Seq} {s n : ℕ} (g : GreedyFrom x s) (hs : s ≤ n)
    (k : ℕ) {a t b : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1)
    (hat : a ≤ t) (htb : t < b) (hlen : b-a ≤ (2:ℝ)^k*(b-t)) :
    S x n t b - S x n a b ≤ (k:ℝ)*((s:ℝ)+1) := by
  have ha' : 1-b ∈ Set.Icc (0:ℝ) 1 := by constructor <;> linarith [hb.1,hb.2]
  have hb' : 1-a ∈ Set.Icc (0:ℝ) 1 := by constructor <;> linarith [ha.1,ha.2]
  have h := mean_extend_right_pow (reflect_from g) hs k ha' hb'
    (show 1-b < 1-t by linarith) (show 1-t ≤ 1-a by linarith)
    (show (1-a)-(1-b) ≤ (2:ℝ)^k*((1-t)-(1-b)) by convert hlen using 1 <;> ring)
  rw [S_reflect g.1, S_reflect g.1] at h
  simp only [sub_sub_cancel] at h
  linarith

def cellMean (x : Seq) (n M i : ℕ) : ℝ :=
  S x n ((i:ℝ)/M) (((i:ℝ)+1)/M)

theorem cell_rise {x : Seq} {s n M i j : ℕ} (g : GreedyFrom x s) (hs : s ≤ n)
    (hij : i ≤ j) (hj : j < M) (k : ℕ) (hlen : j+1-i ≤ 2^k) :
    cellMean x n M j - cellMean x n M i ≤ 2*(k:ℝ)*((s:ℝ)+1) := by
  have hM : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  let a := (i:ℝ)/M
  let t := ((i:ℝ)+1)/M
  let u := (j:ℝ)/M
  let b := ((j:ℝ)+1)/M
  have ha₀ : 0 ≤ a := by dsimp [a]; positivity
  have hb₁ : b ≤ 1 := by
    dsimp [b]
    exact (div_le_one hM).2 (by exact_mod_cast (show j+1 ≤ M by omega))
  have h1 : a < t := by dsimp [a,t]; apply div_lt_div_of_pos_right _ hM; linarith
  have h2 : t ≤ b := by dsimp [t,b]; gcongr
  have h3 : a ≤ u := by dsimp [a,u]; gcongr
  have h4 : u < b := by dsimp [u,b]; apply div_lt_div_of_pos_right _ hM; linarith
  have ha : a ∈ Set.Icc (0:ℝ) 1 := ⟨ha₀,h1.le.trans (h2.trans hb₁)⟩
  have hb : b ∈ Set.Icc (0:ℝ) 1 := ⟨ha₀.trans (h1.le.trans h2),hb₁⟩
  have hlen' : ((j:ℝ)+1)-(i:ℝ) ≤ (2:ℝ)^k := by
    have h : (((j+1-i:ℕ):ℝ)) ≤ (2:ℝ)^k := by exact_mod_cast hlen
    rw [Nat.cast_sub (by omega),Nat.cast_add,Nat.cast_one] at h
    exact h
  have hleft : b-a ≤ (2:ℝ)^k*(t-a) := by
    dsimp [a,b,t]
    rw [div_sub_div_same, div_sub_div_same, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hM.le
    simpa only [add_sub_cancel_left, mul_one] using hlen'
  have hright : b-a ≤ (2:ℝ)^k*(b-u) := by
    have e : b-u = t-a := by
      dsimp [b,u,t,a]
      ring
    rw [e]
    exact hleft
  have hr := mean_extend_right_pow g hs k ha hb h1 h2 hleft
  have hl := mean_extend_left_pow g hs k ha hb h3 h4 hright
  unfold cellMean
  linarith

/-- A bound on rises for short runs controls rises on every run by subdivision. -/
theorem rise_subdivide (f : ℕ → ℝ) {M L : ℕ} (hL : 0 < L)
    {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ i j, i ≤ j → j < M → j-i ≤ L → f j-f i ≤ A)
    (i j : ℕ) (hij : i ≤ j) (hj : j < M) :
    f j-f i ≤ A + (A/(L:ℝ))*((j-i:ℕ):ℝ) := by
  have hLp : (0:ℝ) < L := by exact_mod_cast hL
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases hjL : j-i ≤ L
    · have hz : 0 ≤ (A/(L:ℝ))*((j-i:ℕ):ℝ) := by positivity
      linarith [h i j hij hj hjL]
    · let b := j-L
      have hbi : i ≤ b := by dsimp [b]; omega
      have hb : b < j := by dsimp [b]; omega
      have hd : j-b = L := by dsimp [b]; omega
      have he : j-i = (b-i)+L := by dsimp [b]; omega
      have h₁ := ih b hb hbi (hb.trans hj)
      have h₂ := h b j hb.le hj hd.le
      rw [he, Nat.cast_add, mul_add]
      have h₃ : A/(L:ℝ)*(L:ℝ) = A := div_mul_cancel₀ _ hLp.ne'
      rw [h₃]
      linarith

def dropCount (f : ℕ → ℝ) (T : ℝ) (n : ℕ) :=
  ∑ i ∈ range n, if f i-f (i+1) > T then (1:ℝ) else 0

theorem dropCount_nonneg (f : ℕ → ℝ) (T : ℝ) (n : ℕ) : 0 ≤ dropCount f T n :=
  sum_nonneg fun _ _ => by split_ifs <;> norm_num

/-- Sum the rises between successive large drops. -/
theorem dropCount_charge (f : ℕ → ℝ) {A B T : ℝ} {M : ℕ}
    (hB : 0 ≤ B)
    (hr : ∀ i j, i ≤ j → j ≤ M → f j-f i ≤ A+B*((j-i:ℕ):ℝ))
    (n : ℕ) (hn : n ≤ M) :
    f n-f 0+(T-A)*dropCount f T n ≤ A+B*(n:ℝ) := by
  have aux : ∃ b ≤ n, f n-f 0+(T-A)*dropCount f T n ≤ B*(b:ℝ)+(f n-f b) := by
    induction n with
    | zero => exact ⟨0, le_rfl, by simp [dropCount]⟩
    | succ n ih =>
      have hnm : n ≤ M := by omega
      obtain ⟨b,hb,he⟩ := ih hnm
      have es : dropCount f T (n+1) = dropCount f T n +
          (if f n-f (n+1) > T then (1:ℝ) else 0) := by unfold dropCount; rw [sum_range_succ]
      by_cases h : f n-f (n+1) > T
      · refine ⟨n+1, le_rfl, ?_⟩
        rw [es, if_pos h, Nat.cast_succ, sub_self, add_zero]
        have h' := hr b n hb hnm
        rw [Nat.cast_sub hb] at h'
        nlinarith
      · refine ⟨b, by omega, ?_⟩
        rw [es, if_neg h, add_zero]
        linarith
  obtain ⟨b,hb,he⟩ := aux
  have h := hr b n hb hn
  rw [Nat.cast_sub hb] at h
  nlinarith


theorem dropCount_pos_one {f : ℕ → ℝ} {T : ℝ} {n : ℕ} (h : 0 < dropCount f T n) :
    1 ≤ dropCount f T n := by
  classical
  unfold dropCount at *
  simp only [sum_ite, sum_const, Finset.sum_const_zero, nsmul_eq_mul, mul_one, add_zero] at *
  exact_mod_cast (show 0 < ((range n).filter (fun i => f i-f (i+1)>T)).card by exact_mod_cast h)

theorem cell_endpoints {x : Seq} {s n M : ℕ} (g : GreedyFrom x s) (hs : s ≤ n)
    (hM : 0 < M) :
    -(2*seedBound s) ≤ cellMean x n M (M-1) - cellMean x n M 0 := by
  have hp : (0:ℝ)<M := by exact_mod_cast hM
  let t := (1:ℝ)/M
  have ht : t ∈ Set.Icc (0:ℝ) 1 := ⟨by dsimp [t]; positivity,
    (div_le_one hp).2 (by exact_mod_cast hM)⟩
  have ht' : 0 < t := by dsimp [t]; positivity
  have helper {y : Seq} (gy : GreedyFrom y s) : S y n 0 t ≤ seedBound s := by
    unfold S
    rw [H_zero_of_unit gy.1, sub_zero, sub_zero]
    exact (div_le_iff₀ ht').2 (boundary_from gy hs ht)
  have hfirst : cellMean x n M 0 ≤ seedBound s := by
    simpa [cellMean, t] using helper g
  have hlast : -cellMean x n M (M-1) ≤ seedBound s := by
    have h := helper (reflect_from g)
    rw [S_reflect g.1, sub_zero] at h
    unfold cellMean
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    have e : ((M:ℝ)-1)/M = 1-t := by
      dsimp [t]; field_simp [hp.ne']
    rw [e, sub_add_cancel, div_self hp.ne']
    exact h
  linarith

theorem cell_drop_tail {x : Seq} {s n M : ℕ} (g : GreedyFrom x s) (hs : s ≤ n)
    (hM : 0 < M) (k : ℕ) :
    dropCount (cellMean x n M) (8*((k:ℝ)+1)*((s:ℝ)+1)+2*seedBound s) (M-1)
      ≤ (M:ℝ)/(2:ℝ)^k := by
  let f := cellMean x n M
  let A : ℝ := 2*((k:ℝ)+1)*((s:ℝ)+1)
  let L : ℕ := 2^k
  let T := 4*A+2*seedBound s
  have ha : 0 < A := by dsimp [A]; positivity
  have hp : 0 < L := by dsimp [L]; positivity
  have hC : 0 ≤ 2*seedBound s := by
    unfold seedBound
    linarith [le_max_left (1/2:ℝ) (s:ℝ)]
  have hr : ∀ i j, i ≤ j → j ≤ M-1 → f j-f i ≤ A+A/(L:ℝ)*((j-i:ℕ):ℝ) := by
    intro i j hij hj
    apply rise_subdivide f (M := M) hp ha.le _ i j hij (by omega)
    intro i j hij hj hlen
    have h := cell_rise g hs hij hj (k+1) (by
      have hpower : 0 < (2:ℕ)^k := by positivity
      rw [pow_succ]
      dsimp [L] at hlen
      omega)
    simpa [A,f,Nat.cast_succ] using h
  have hq := dropCount_charge f (T := T) (by positivity : 0 ≤ A/(L:ℝ)) hr (M-1) le_rfl
  have he := cell_endpoints g hs hM
  change -(2*seedBound s) ≤ f (M-1)-f 0 at he
  have hsub : ((M-1:ℕ):ℝ) ≤ M := by exact_mod_cast Nat.sub_le M 1
  have hm := mul_le_mul_of_nonneg_left hsub (by positivity : 0 ≤ A/(L:ℝ))
  have hLp : (0:ℝ) < L := by exact_mod_cast hp
  suffices h : dropCount f T (M-1) ≤ (M:ℝ)/(L:ℝ) by
    have heq : T = 8*((k:ℝ)+1)*((s:ℝ)+1)+2*seedBound s := by dsimp [T,A]; ring
    rw [heq] at h
    simpa [f,L] using h
  have hn := dropCount_nonneg f T (M-1)
  rcases hn.eq_or_lt with h | h
  · rw [← h]; positivity
  · have h1 := dropCount_pos_one h
    have h2 := mul_le_mul_of_nonneg_left h1 ha.le
    have h3 := mul_le_mul_of_nonneg_left h1 hC
    have he' : A/(L:ℝ)*(M:ℝ) = A*((M:ℝ)/(L:ℝ)) := by ring
    rw [he'] at hm
    apply le_of_mul_le_mul_left _ ha
    unfold T at hq
    nlinarith only [hq,he,hm,h2,h3, mul_nonneg ha.le hn]


/-- Convert geometrically decaying counts into bounds on every integer moment. -/
theorem row_moment_of_tail (f : ℕ → ℝ) (m d : ℕ) {A W : ℝ} (hA : 0 < A) (hW : 0 ≤ W)
    (hsize : (m:ℝ) ≤ W) (hrise : ∀ i < m, f (i+1)-f i ≤ A)
    (htail : ∀ k : ℕ, dropCount f (A*((k:ℝ)+1)) m ≤ W/(2:ℝ)^k) :
    (∑ i ∈ range m, |f (i+1)-f i|^d) ≤
      W * (A^d + ∑' k : ℕ, (A*((k:ℝ)+2))^d / (2:ℝ)^k) := by
  let w (k : ℕ) := (A*((k:ℝ)+2))^d/(2:ℝ)^k
  have hw : ∀ k, 0 ≤ w k := fun k => by dsimp [w]; positivity
  have hsum : Summable w := by
    have h := summable_pow_mul_geometric_of_norm_lt_one d
      (r := (1/2:ℝ)) (by norm_num)
    have h' : Summable (fun k : ℕ => (((k+2:ℕ):ℝ)^d)*(1/2:ℝ)^(k+2)) :=
      (summable_nat_add_iff 2).2 h
    convert h'.mul_left (4*A^d) using 1
    ext k
    dsimp [w]
    simp only [Nat.cast_add, Nat.cast_ofNat, mul_pow, pow_add, inv_pow, one_div]
    ring
  obtain ⟨J,hJ⟩ := exists_nat_gt
    ((∑ i ∈ range m, |f (i+1)-f i|)/A)
  have hbound (i : ℕ) (hi : i ∈ range m) : |f (i+1)-f i| ≤ A*((J:ℝ)+1) := by
    have h := single_le_sum (f := fun i => |f (i+1)-f i|)
      (fun j _ => abs_nonneg _) hi
    have h' := (div_lt_iff₀ hA).1 hJ
    nlinarith
  let term (i k : ℕ) := if f i-f (i+1)>A*((k:ℝ)+1) then (A*((k:ℝ)+2))^d else 0
  have hpoint (i : ℕ) (hi : i ∈ range m) :
      |f (i+1)-f i|^d ≤ A^d + ∑ k ∈ range J, term i k := by
    have hsum0 : 0 ≤ ∑ k ∈ range J, term i k :=
      sum_nonneg fun j _ => by dsimp [term]; split_ifs <;> positivity
    by_cases hh : |f (i+1)-f i| ≤ A
    · linarith [pow_le_pow_left₀ (abs_nonneg _) hh d]
    have hex : ∃ l : ℕ, |f (i+1)-f i| ≤ A*((l:ℝ)+1) := ⟨J,hbound i hi⟩
    let l := Nat.find hex
    have hle : |f (i+1)-f i| ≤ A*((l:ℝ)+1) := Nat.find_spec hex
    have hlj : l ≤ J := Nat.find_min' hex (hbound i hi)
    have hl0 : 0 < l := by
      by_contra! h
      have he : l=0 := by omega
      simp [he] at hle
      exact hh hle
    let k := l-1
    have hk : k < l := by dsimp [k]; omega
    have hmin : A*((k:ℝ)+1) < |f (i+1)-f i| := lt_of_not_ge (Nat.find_min hex hk)
    have hneg : f (i+1)-f i < 0 := by
      by_contra! h
      rw [abs_of_nonneg h] at hh
      exact hh (hrise i (mem_range.mp hi))
    rw [abs_of_neg hneg] at hmin
    have hcast : (l:ℝ) = (k:ℝ)+1 := by exact_mod_cast (show l=k+1 by dsimp [k]; omega)
    have hterm : term i k = (A*((k:ℝ)+2))^d := by
      unfold term
      rw [if_pos (by linarith : A*((k:ℝ)+1) < f i-f (i+1))]
    have hsingle := single_le_sum (f := term i)
      (fun j _ => by unfold term; split_ifs <;> positivity)
      (mem_range.mpr (hk.trans_le hlj))
    rw [hterm] at hsingle
    have hb : |f (i+1)-f i| ≤ A*((k:ℝ)+2) := by rw [hcast] at hle; linarith
    linarith [pow_le_pow_left₀ (abs_nonneg _) hb d, pow_nonneg hA.le d]
  have htotal := sum_le_sum (s := range m) hpoint
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, card_range, sum_comm] at htotal
  have hterms : ∀ k ∈ range J, (∑ i ∈ range m, term i k) ≤ W*w k := by
    intro k _
    have e : (∑ i ∈ range m, term i k) = dropCount f (A*((k:ℝ)+1)) m*(A*((k:ℝ)+2))^d := by
      unfold dropCount
      rw [sum_mul]
      apply sum_congr rfl
      intro i _
      unfold term
      split_ifs <;> ring
    rw [e]
    calc
      _ ≤ W/(2:ℝ)^k*(A*((k:ℝ)+2))^d := mul_le_mul_of_nonneg_right (htail k) (by positivity)
      _ = W*w k := by dsimp [w]; ring
  have hterms' := sum_le_sum hterms
  rw [← mul_sum] at hterms'
  have ht := mul_le_mul_of_nonneg_left (hsum.sum_le_tsum (range J) (fun k _ => hw k)) hW
  have hbase := mul_le_mul_of_nonneg_right hsize (pow_nonneg hA.le d)
  change _ ≤ W*(A^d+∑' k, w k)
  linarith [show W*(A^d+∑' k,w k)=W*A^d+W*(∑' k,w k) by ring]


theorem cell_row_moment (s d : ℕ) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ (x : Seq) (n M : ℕ), GreedyFrom x s → s ≤ n → 0 < M →
      (∑ i ∈ range (M-1), |cellMean x n M (i+1)-cellMean x n M i|^d) ≤ (M:ℝ)*V := by
  let A : ℝ := 10*((s:ℝ)+1)
  let V := A^d + ∑' k : ℕ, (A*((k:ℝ)+2))^d/(2:ℝ)^k
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨V, ?_, ?_⟩
  · unfold V
    exact add_nonneg (pow_nonneg hA.le _) (tsum_nonneg fun _ => by positivity)
  intro x n M g hs hM
  apply row_moment_of_tail _ _ _ hA (Nat.cast_nonneg M)
    (by exact_mod_cast Nat.sub_le M 1)
  · intro i hi
    have h := cell_rise g hs (show i ≤ i+1 by omega) (show i+1 < M by omega)
      1 (by omega)
    norm_num at h
    dsimp [A]
    linarith [(Nat.cast_nonneg s : (0:ℝ) ≤ s)]
  · intro k
    apply le_trans _ (cell_drop_tail g hs hM k)
    apply sum_le_sum
    intro i _
    have hB : seedBound s ≤ (s:ℝ)+1 := by
      unfold seedBound
      exact max_le (by nlinarith [(Nat.cast_nonneg s : (0:ℝ) ≤ s)]) (by linarith)
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg _
    have h : 8*((k:ℝ)+1)*((s:ℝ)+1)+2*seedBound s ≤ A*((k:ℝ)+1) := by
      dsimp [A]
      nlinarith [mul_nonneg hk (show (0:ℝ) ≤ (s:ℝ)+1 by positivity)]
    split_ifs with h' h'' <;> norm_num at *
    linarith

theorem sum_pairs {R : Type*} [AddCommMonoid R] (f : ℕ → R) (n : ℕ) :
    (∑ i ∈ range (2*n),f i) = ∑ i ∈ range n, (f (2*i)+f (2*i+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega, sum_range_succ, sum_range_succ,
      sum_range_succ, ih, add_assoc]

theorem sum_even_with_last {R : Type*} [AddCommMonoid R] (f : ℕ → R) (n : ℕ)
    (h : ∀ i < n, f (2*i+1)=0) :
    (∑ i ∈ range (2*n+1), f i) = ∑ i ∈ range (n+1), f (2*i) := by
  rw [sum_range_succ, sum_pairs, sum_range_succ]
  congr 1
  apply sum_congr rfl
  intro i hi
  rw [h i (mem_range.mp hi), add_zero]

#print axioms cell_row_moment
end
end Kritzinger
