import Kritzinger.Moments
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.MeanInequalities

namespace Kritzinger
open Finset
noncomputable section

theorem symmetrized_power (u v : ℝ) {r : ℕ} (hr : 0 < r) :
    ((u+v)^(2*r)+(u-v)^(2*r))/2 ≤ (u^2+(2:ℝ)^(2*r)*v^2)^r := by
  let term (i : ℕ) :=
    (u^i * v^(2*r-i) * ((2*r).choose i:ℝ) +
      u^i * (-v)^(2*r-i) * ((2*r).choose i:ℝ))/2
  have hl : ((u+v)^(2*r)+(u-v)^(2*r))/2 = ∑ i ∈ range (2*r+1), term i := by
    rw [sub_eq_add_neg, add_pow, add_pow, ← sum_add_distrib, sum_div]
  rw [hl, sum_even_with_last term r, add_pow]
  · apply sum_le_sum
    intro i hi
    have hir : i ≤ r := by simpa using Nat.le_of_lt_succ (mem_range.mp hi)
    have he : 2*r - 2*i = 2*(r-i) := by omega
    have hv : (-v)^(2*(r-i)) = v^(2*(r-i)) := by
      rw [pow_mul, pow_mul]
      congr 1
      ring
    unfold term
    rw [he,hv, pow_mul u, pow_mul v, mul_pow]
    have hnon : 0 ≤ (u^2)^i * (v^2)^(r-i) := by positivity
    have hb : ((2*r).choose (2*i):ℝ) ≤ ((2:ℝ)^(2*r))^(r-i)*(r.choose i:ℝ) := by
      rcases eq_or_lt_of_le hir with heq | hlt
      · subst i
        simp
      · have h1 : ((2*r).choose (2*i):ℝ) ≤ (2:ℝ)^(2*r) := by
          exact_mod_cast (Nat.choose_le_two_pow (2*r) (2*i) (by omega)).le
        have h2 : (2:ℝ)^(2*r) ≤ ((2:ℝ)^(2*r))^(r-i) := by
          simpa using (pow_le_pow_right₀ (show (1:ℝ) ≤ (2:ℝ)^(2*r) by
            exact one_le_pow₀ (by norm_num)) (show 1 ≤ r-i by omega))
        have h3 : (1:ℝ) ≤ r.choose i := by
          exact_mod_cast Nat.choose_pos hir
        have hp : 0 ≤ ((2:ℝ)^(2*r))^(r-i) := by positivity
        have hh := mul_le_mul_of_nonneg_left h3 hp
        rw [mul_one] at hh
        exact h1.trans (h2.trans hh)
    nlinarith only [mul_le_mul_of_nonneg_left hb hnon]
  · intro i hi
    unfold term
    rw [show 2*r-(2*i+1)=2*(r-i-1)+1 by omega, pow_succ (-v), pow_mul (-v)]
    rw [show (-v)^2=v^2 by ring, pow_succ v, pow_mul v]
    ring


def powerMean (m r : ℕ) (f : ℕ → ℝ) :=
  ((∑ i ∈ range m, (f i)^r)/(m:ℝ)) ^ (1/(r:ℝ))

theorem powerMean_add (m : ℕ) {r : ℕ} (hr : 0 < r)
    (f g : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    powerMean m r (fun i => f i+g i) ≤ powerMean m r f+powerMean m r g := by
  have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
  have h := Real.Lp_add_le_of_nonneg (s := range m) (f := f) (g := g)
    hr' (fun i _ => hf i) (fun i _ => hg i)
  simp only [Real.rpow_natCast] at h
  have f0 : 0 ≤ ∑ i ∈ range m, (f i)^r := sum_nonneg (fun i _ => pow_nonneg (hf i) _)
  have g0 : 0 ≤ ∑ i ∈ range m, (g i)^r := sum_nonneg (fun i _ => pow_nonneg (hg i) _)
  have fg0 : 0 ≤ ∑ i ∈ range m, (f i+g i)^r :=
    sum_nonneg (fun i _ => pow_nonneg (add_nonneg (hf i) (hg i)) _)
  unfold powerMean
  rw [Real.div_rpow fg0 (Nat.cast_nonneg m), Real.div_rpow f0 (Nat.cast_nonneg m),
    Real.div_rpow g0 (Nat.cast_nonneg m), ← add_div]
  exact div_le_div_of_nonneg_right h (by positivity)

theorem powerMean_smul (m : ℕ) {r : ℕ} (hr : 0 < r) {c : ℝ} (hc : 0 ≤ c)
    (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) :
    powerMean m r (fun i => c*f i) = c*powerMean m r f := by
  have hn : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hz : 0 ≤ (∑ i ∈ range m, (f i)^r)/(m:ℝ) :=
    div_nonneg (sum_nonneg (fun i _ => pow_nonneg (hf i) _)) (Nat.cast_nonneg m)
  unfold powerMean
  simp_rw [mul_pow]
  rw [← mul_sum, mul_div_assoc, Real.mul_rpow (pow_nonneg hc _) hz,
    ← Real.rpow_natCast, ← Real.rpow_mul hc]
  rw [mul_one_div_cancel hn, Real.rpow_one]

theorem dyadic_average (x : Seq) (n m i : ℕ) (hm : 0 < m) :
    cellMean x n m i = (cellMean x n (2*m) (2*i) + cellMean x n (2*m) (2*i+1))/2 := by
  have hp : (0:ℝ) < m := by exact_mod_cast hm
  have hnn := hp.ne'
  have h2 : (2:ℝ)*m ≠ 0 := by positivity
  unfold cellMean S
  push_cast
  have ha : (2*(i:ℝ))/(2*(m:ℝ)) = (i:ℝ)/m := by field_simp; ring
  have hb : (2*(i:ℝ)+1+1)/(2*(m:ℝ)) = ((i:ℝ)+1)/m := by
    field_simp
    ring
  rw [ha, hb]
  have he : (((i:ℝ)+1)/m-(i:ℝ)/m) = 1/(m:ℝ) := by ring
  have h₁ : ((2*(i:ℝ)+1)/(2*(m:ℝ))-(i:ℝ)/m) = 1/(2*(m:ℝ)) := by
    field_simp
    ring
  have h₂ : (((i:ℝ)+1)/m-(2*(i:ℝ)+1)/(2*(m:ℝ))) = 1/(2*(m:ℝ)) := by
    field_simp
    ring
  rw [he,h₁,h₂]
  simp only [div_div_eq_mul_div, div_one]
  ring

def dyadicEnergy (x : Seq) (n j r : ℕ) :=
  powerMean (2^j) r (fun i => (cellMean x n (2^j) i)^2)

theorem dyadic_step {x : Seq} {n r : ℕ} (hr : 0 < r)
    (V : ℝ)
    (hrow : ∀ M : ℕ, 0 < M →
       (∑ i ∈ range (M-1), |cellMean x n M (i+1)-cellMean x n M i|^(2*r)) ≤ (M:ℝ)*V)
    (j : ℕ) :
    dyadicEnergy x n (j+1) r ≤ dyadicEnergy x n j r + (2:ℝ)^(2*r)*(2*V)^(1/(r:ℝ)) := by
  let m : ℕ := 2^j
  have hm : 0 < m := by dsimp [m]; positivity
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  let f := cellMean x n (2*m)
  let a := cellMean x n m
  let b (i : ℕ) := (f (2*i+1)-f (2*i))/2
  let C : ℝ := (2:ℝ)^(2*r)
  have hp : 2^(j+1) = 2*m := by dsimp [m]; rw [pow_succ,mul_comm]
  have hav (i : ℕ) : a i = (f (2*i)+f (2*i+1))/2 := dyadic_average x n m i hm
  have hpair (i : ℕ) : ((f (2*i))^2)^r+((f (2*i+1))^2)^r ≤
      2*((a i)^2+C*(b i)^2)^r := by
    have h := symmetrized_power (a i) (b i) hr
    rw [hav i] at h
    dsimp [b] at h
    rw [show (f (2*i)+f (2*i+1))/2 + (f (2*i+1)-f (2*i))/2 = f (2*i+1) by ring,
      show (f (2*i)+f (2*i+1))/2 - (f (2*i+1)-f (2*i))/2 = f (2*i) by ring] at h
    change _ ≤ 2*((a i)^2+(2:ℝ)^(2*r)*(b i)^2)^r
    rw [hav i, ← pow_mul, ← pow_mul]
    linarith
  have hpow : powerMean (2*m) r (fun i => (f i)^2) ≤
      powerMean m r (fun i => (a i)^2+C*(b i)^2) := by
    unfold powerMean
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    rw [sum_pairs]
    have he := sum_le_sum (s := range m) fun i _ => hpair i
    rw [← mul_sum] at he
    push_cast
    apply (div_le_div_iff₀ (by positivity) hm').2
    nlinarith only [mul_le_mul_of_nonneg_right he hm'.le]
  have hbsum : (∑ i ∈ range m, ((b i)^2)^r) ≤ (2*m:ℕ)*V := by
    have hh : ∀ i ∈ range m, ((b i)^2)^r ≤ |f (2*i+1)-f (2*i)|^(2*r) := by
      intro i _
      rw [← pow_mul]
      have e : (b i)^(2*r) = (|b i|)^(2*r) := by
        rw [pow_mul, pow_mul, sq_abs]
      rw [e]
      apply pow_le_pow_left₀ (abs_nonneg _) _ _
      dsimp [b]
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith [abs_nonneg (f (2*i+1)-f (2*i))]
    apply (sum_le_sum hh).trans _
    let w (i : ℕ) := |f (i+1)-f i|^(2*r)
    have e : (∑ i ∈ range m, w (2*i)) = ∑ i ∈ (range m).image (fun i => 2*i), w i := by
      rw [sum_image]
      intro i _ j _ hij
      omega
    change (∑ i ∈ range m, w (2*i)) ≤ _
    rw [e]
    apply (sum_le_sum_of_subset_of_nonneg (t := range (2*m-1)) _ (fun i _ _ => by positivity)).trans
      (hrow (2*m) (by omega))
    intro i hi
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hi
    exact mem_range.mpr (by have := mem_range.mp hk; omega)
  have hbp : powerMean m r (fun i => (b i)^2) ≤ (2*V)^(1/(r:ℝ)) := by
    unfold powerMean
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    apply (div_le_iff₀ hm').2
    push_cast at hbsum
    linarith only [hbsum, show (2*V)*(m:ℝ)=2*(m:ℝ)*V by ring]
  unfold dyadicEnergy
  rw [hp]
  apply hpow.trans _
  have hM := powerMean_add m hr (fun i => (a i)^2) (fun i => C*(b i)^2)
    (fun _ => sq_nonneg _) (fun _ => by dsimp [C]; positivity)
  rw [powerMean_smul m hr (by dsimp [C]; positivity) _ (fun _ => sq_nonneg _)] at hM
  exact hM.trans (add_le_add_left (mul_le_mul_of_nonneg_left hbp (by dsimp [C]; positivity)) _)

#print axioms dyadic_step
end
end Kritzinger
