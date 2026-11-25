import Kritzinger

namespace Kritzinger
open Finset MeasureTheory
noncomputable section

def GreedyFrom (x : Seq) (s : ℕ) : Prop :=
  (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) ∧
  ∀ n ≥ s, ∀ t ∈ Set.Icc (0 : ℝ) 1, K x n t ≤ K x n (x n)

theorem reflect_from {x : Seq} {s : ℕ} (g : GreedyFrom x s) :
    GreedyFrom (reflect x) s := by
  constructor
  · intro i
    have hi := g.1 i
    change 0 ≤ 1-x i ∧ 1-x i ≤ 1
    constructor <;> linarith [hi.1, hi.2]
  · intro n hn t ht
    have h := g.2 n hn (1-t) (by constructor <;> linarith [ht.1, ht.2])
    unfold K at *
    rw [H_reflect_of_unit g.1, H_reflect_of_unit g.1]
    unfold reflect
    rw [sub_sub_cancel]
    nlinarith

theorem D_seed (x : Seq) (s : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    |D x s t| ≤ s := by
  have h0 : 0 ≤ (∑ i ∈ range s, if x i < t then (1:ℝ) else 0) :=
    sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have h1 : (∑ i ∈ range s, if x i < t then (1:ℝ) else 0) ≤ s := by
    simpa using (sum_le_sum fun (i : ℕ) (_ : i ∈ range s) =>
      show (if x i < t then (1:ℝ) else 0) ≤ 1 by split_ifs <;> norm_num)
  have h2 := mul_nonneg (Nat.cast_nonneg s : (0:ℝ) ≤ s) ht.1
  have h3 := mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg s : (0:ℝ) ≤ s)
  apply abs_le.mpr
  unfold D
  constructor <;> linarith

theorem S_seed (x : Seq) (s : ℕ) {a t : ℝ}
    (ha : 0 ≤ a) (ht : t ≤ 1) (hat : a < t) :
    |S x s a t| ≤ s := by
  have hh : ∀ i, 0 ≤ max 0 (t-x i) - max 0 (a-x i) ∧
      max 0 (t-x i) - max 0 (a-x i) ≤ t-a := by
    intro i
    rcases le_total (x i) a with h | h
    · rw [max_eq_right (by linarith : 0 ≤ t-x i), max_eq_right (sub_nonneg.mpr h)]
      constructor <;> linarith
    · rw [max_eq_left (sub_nonpos.mpr h)]
      constructor
      · linarith [le_max_left 0 (t-x i)]
      · rw [sub_zero]
        exact max_le (by linarith) (by linarith)
  have h0 := sum_nonneg (s := range s) fun i _ => (hh i).1
  have h1 := sum_le_sum (s := range s) fun i _ => (hh i).2
  simp only [sum_sub_distrib] at h0 h1
  simp only [sum_const, nsmul_eq_mul, card_range] at h1
  have hc0 := mul_nonneg (Nat.cast_nonneg s : (0:ℝ) ≤ s) (show 0 ≤ (t+a)/2 by linarith)
  have hc1 := mul_le_mul_of_nonneg_left (show (t+a)/2 ≤ 1 by linarith)
    (Nat.cast_nonneg s : (0:ℝ) ≤ s)
  have hp := sub_pos.mpr hat
  have h2 := mul_nonneg hc0 hp.le
  have h3 := mul_le_mul_of_nonneg_right hc1 hp.le
  apply abs_le.mpr
  unfold S H
  constructor
  · apply (le_div_iff₀ hp).2
    nlinarith only [h0, h3]
  · apply (div_le_iff₀ hp).2
    nlinarith only [h1, h2]

theorem H_zero_of_unit {x : Seq} (hx : ∀ i, x i ∈ Set.Icc (0:ℝ) 1) (N : ℕ) :
    H x N 0 = 0 := by
  have hz : (∑ i ∈ range N, max 0 ((0:ℝ)-x i)) = 0 :=
    sum_eq_zero fun i _ => max_eq_left (by linarith [(hx i).1])
  simp only [H,hz]
  ring

def seedBound (s : ℕ) : ℝ := max (1/2) (s:ℝ)

theorem boundary_from {x : Seq} {s n : ℕ} (g : GreedyFrom x s) (hn : s ≤ n)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : H x n t ≤ seedBound s*t := by
  induction n, hn using Nat.le_induction generalizing t with
  | base =>
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, H_zero_of_unit g.1]
      simp
    · have hs := (abs_le.mp (S_seed x s le_rfl ht.2 h)).2
      unfold S at hs
      rw [H_zero_of_unit g.1, sub_zero, sub_zero] at hs
      exact ((div_le_iff₀ h).1 hs).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) ht.1)
  | succ n hn ih =>
    rcases le_total t (x n) with h | h
    · rw [H_succ, max_eq_left (sub_nonpos.mpr h)]
      nlinarith [ih ht, sq_nonneg t]
    · have hc := cone_step n (g.2 n hn) ht
      rw [abs_of_nonneg (sub_nonneg.mpr h), H_succ x n (x n), sub_self, max_self] at hc
      have hb := mul_le_mul_of_nonneg_right (le_max_left (1/2:ℝ) (s:ℝ)) (sub_nonneg.mpr h)
      unfold seedBound at *
      nlinarith only [hc, ih (g.1 n), sq_nonneg (x n), hb]

theorem trace_from {x : Seq} {s : ℕ} (g : GreedyFrom x s) {N : ℕ} (hN : 0 < N)
    {n : ℕ} (hs : s ≤ n) (hn : n ≤ N) {a t : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hat : a < t) :
    R x n a t ≤ 2*seedBound s + 1 + max 0 (Real.log (2*(N:ℝ)*(t-a))) := by
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  induction n, hs using Nat.le_induction generalizing a with
  | base =>
    have hd := (abs_le.mp (D_seed x s ht)).2
    have hm := (abs_le.mp (S_seed x s ha.1 ht.2 hat)).1
    have hb : (s:ℝ) ≤ seedBound s := le_max_right _ _
    have hlog := le_max_left 0 (Real.log (2*(N:ℝ)*(t-a)))
    unfold R
    linarith
  | succ n hs ih =>
    have hn' : n ≤ N := by omega
    by_cases hc : a < x n ∧ x n < t
    · have e := inside_step n (g.2 n hs) ha ht hc.1 hc.2
      have hh := sub_pos.mpr hc.2
      by_cases hshort : 2*(N:ℝ)*(t-x n) < 1
      · have he : ∀ i < n, ¬ (x n < x i ∧ x i < t) := by
          intro i hi h
          have hs := separation_step (g.2 n hs) hi
          rw [abs_of_neg (sub_neg.mpr h.1)] at hs
          have hnle : (n:ℝ)+1 ≤ N := by exact_mod_cast hn
          have hd : 1/(2*(N:ℝ)) ≤ 1/(2*((n:ℝ)+1)) :=
            one_div_le_one_div_of_le (by positivity) (by linarith)
          have hold := hd.trans hs
          have hh' : t-x n < 1/(2*(N:ℝ)) := by
            apply (lt_div_iff₀ (by positivity)).2
            linarith [show (t-x n)*(2*(N:ℝ)) = 2*(N:ℝ)*(t-x n) by ring]
          linarith
        have hz := empty_interval x n hc.2 he
        have hr : 0 ≤ (t-x n)/(t-a) := div_nonneg (sub_nonneg.mpr hc.2.le) (sub_nonneg.mpr hat.le)
        have hm := le_max_left 0 (Real.log (2*(N:ℝ)*(t-a)))
        have hb : 0 ≤ seedBound s := (by norm_num : (0:ℝ) ≤ 1/2).trans (le_max_left _ _)
        linarith
      · have eih := ih hn' (g.1 n) hc.2
        have hp : 0 < 2*(N:ℝ)*(t-x n) := by positivity
        have hlog : 0 ≤ Real.log (2*(N:ℝ)*(t-x n)) :=
          Real.log_nonneg (le_of_not_gt hshort)
        rw [max_eq_right hlog] at eih
        have hd := Real.log_le_sub_one_of_pos (div_pos hh (sub_pos.mpr hat))
        have hlogeq : Real.log ((t-x n)/(t-a)) =
            Real.log (2*(N:ℝ)*(t-x n)) - Real.log (2*(N:ℝ)*(t-a)) := by
          have hp' : 0 < 2*(N:ℝ)*(t-a) := mul_pos (by positivity) (sub_pos.mpr hat)
          rw [← Real.log_div (ne_of_gt hp) (ne_of_gt hp')]
          congr 1
          field_simp [ne_of_gt hNp, ne_of_gt (sub_pos.mpr hat)]
          ring
        rw [hlogeq] at hd
        have hm := le_max_right 0 (Real.log (2*(N:ℝ)*(t-a)))
        linarith
    · have e := outside x n hat (by
        by_cases h : x n ≤ a
        · exact Or.inl h
        · exact Or.inr (le_of_not_gt (fun h' => hc ⟨lt_of_not_ge h,h'⟩)))
      linarith [ih hn' ha hat]


theorem upper_from {x : Seq} {s : ℕ} (g : GreedyFrom x s) {N : ℕ} (hN : 0 < N) (hs : s ≤ N)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    D x N t ≤ 3*seedBound s + 1 + Real.log (2*(N:ℝ)) := by
  have hNp : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hB : 0 ≤ seedBound s := (by norm_num : (0:ℝ) ≤ 1/2).trans (le_max_left _ _)
  have hlog : 0 ≤ Real.log (2*(N:ℝ)) := Real.log_nonneg (by linarith)
  rcases eq_or_lt_of_le ht.1 with he | hp
  · subst t
    have hz : (∑ i ∈ range N, if x i < 0 then (1:ℝ) else 0) = 0 :=
      sum_eq_zero fun i _ => if_neg (not_lt.mpr (g.1 i).1)
    simp [D, hz]
    linarith
  have h := trace_from g hN hs le_rfl (by constructor <;> norm_num : (0:ℝ) ∈ Set.Icc 0 1) ht hp
  have H0 : H x N 0 = 0 := by
    have hz : (∑ i ∈ range N, max 0 ((0:ℝ)-x i)) = 0 :=
      sum_eq_zero fun i _ => max_eq_left (by linarith [(g.1 i).1])
    simp only [H, hz]
    ring
  have hm : S x N 0 t ≤ seedBound s := by
    unfold S
    rw [H0, sub_zero, sub_zero]
    exact (div_le_iff₀ hp).2 (by linarith [boundary_from g hs ht])
  have hl : Real.log (2*(N:ℝ)*t) ≤ Real.log (2*(N:ℝ)) :=
    Real.log_le_log (by positivity) (by
      simpa using mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ 2*(N:ℝ) by positivity))
  simp only [sub_zero] at h
  have hh := max_le hlog hl
  unfold R at h
  linarith

theorem star_discrepancy_from_seed {x : Seq} {s N : ℕ} (g : GreedyFrom x s)
    (hN : 0 < N) (hs : s ≤ N) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    |D x N t| ≤ 3*seedBound s + 1 + Real.log (2*(N:ℝ)) := by
  apply abs_of_reflected_upper g.1 hN ?_ (fun _ => upper_from g hN hs)
    (fun _ => upper_from (reflect_from g) hN hs) ht
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hB : (1:ℝ)/2 ≤ seedBound s := le_max_left _ _
  linarith [Real.log_nonneg (show 1 ≤ 2*(N:ℝ) by linarith)]

theorem chord_from_seed {x : Seq} {s n : ℕ} (g : GreedyFrom x s) (hs : s ≤ n) {a t b : ℝ}
    (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1)
    (hat : a < t) (htb : t < b) :
    chord x n a t b ≤ ((s:ℝ)+1)* (Real.sqrt (t-a)*Real.sqrt (b-t)) := by
  have hC : (1:ℝ) ≤ (s:ℝ)+1 := by simp
  induction n, hs using Nat.le_induction generalizing a t b with
  | base =>
    have hp := sub_pos.mpr hat
    have hq := sub_pos.mpr htb
    have hsum := add_pos hp hq
    have hL := (abs_le.mp (S_seed x s ha.1 (htb.le.trans hb.2) hat)).1
    have hR := (abs_le.mp (S_seed x s (ha.1.trans hat.le) hb.2 htb)).2
    have he : chord x s a t b =
        (t-a)*(b-t)/((t-a)+(b-t)) * (S x s t b - S x s a t) := by
      unfold chord S
      rw [show (t-a)+(b-t)=b-a by ring]
      field_simp [hp.ne', hq.ne', (sub_pos.mpr (hat.trans htb)).ne']
      ring
    have hsmall : (t-a)*(b-t)/((t-a)+(b-t)) ≤
        Real.sqrt (t-a)*Real.sqrt (b-t)/2 := by
      have ha' := Real.sq_sqrt hp.le
      have hb' := Real.sq_sqrt hq.le
      have h₁ : 2*Real.sqrt (t-a)*Real.sqrt (b-t) ≤ (t-a)+(b-t) := by
        nlinarith [sq_nonneg (Real.sqrt (t-a)-Real.sqrt (b-t))]
      have h₂ := mul_le_mul_of_nonneg_right h₁
        (mul_nonneg (Real.sqrt_nonneg (t-a)) (Real.sqrt_nonneg (b-t)))
      apply (div_le_iff₀ hsum).2
      have he' : (Real.sqrt (t-a)*Real.sqrt (b-t))^2 = (t-a)*(b-t) := by
        rw [mul_pow, ha', hb']
      nlinarith only [h₂, he']
    have hnon : 0 ≤ (t-a)*(b-t)/((t-a)+(b-t)) :=
      div_nonneg (mul_nonneg hp.le hq.le) hsum.le
    rw [he]
    calc
      _ ≤ ((t-a)*(b-t)/((t-a)+(b-t)))*(2*(s:ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hnon
      _ ≤ (Real.sqrt (t-a)*Real.sqrt (b-t)/2)*(2*(s:ℝ)) :=
        mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg (Real.sqrt_nonneg (t-a)) (Real.sqrt_nonneg (b-t))]
  | succ n hs ih =>
    have hp := sub_pos.mpr hat
    have hq := sub_pos.mpr htb
    have hn := ne_of_gt (sub_pos.mpr (hat.trans htb))
    by_cases hc : a < x n ∧ x n < b
    · have hc' := g.1 n
      have birth := chord_birth_step n (g.2 n hs) ha hb hc.1 hc.2
      rcases lt_trichotomy (x n) t with h | h | h
      · have hcb := ne_of_gt (sub_pos.mpr hc.2)
        have hsplit : chord x (n+1) a t b = chord x (n+1) (x n) t b +
            (b-t)/(b-x n)*chord x (n+1) a (x n) b := by
          unfold chord
          field_simp [hn,hcb]
          ring
        have hm := mul_le_mul_of_nonneg_left birth
          (div_nonneg hq.le (sub_nonneg.mpr hc.2.le))
        have he : (b-t)/(b-x n)*((x n-a)*(b-x n)/(b-a)) =
            (b-t)*((t-a)-(t-x n))/((t-a)+(b-t)) := by
          rw [show (t-a)+(b-t)=b-a by ring]
          field_simp [hn,hcb]
          ring
        rw [he] at hm
        rw [hsplit, chord_outside x n h htb (Or.inl le_rfl)]
        have hfin := sqrt_step hp hq (sub_nonneg.mpr h.le) (by linarith : t-x n ≤ t-a)
        have hmul := mul_nonneg (sub_nonneg.mpr h.le) hq.le
        have hn' : 0 ≤ (b-t)*((t-a)-(t-x n))/((t-a)+(b-t)) :=
          div_nonneg (mul_nonneg hq.le (by linarith [hc.1])) (add_pos hp hq).le
        have hs₁ := mul_le_mul_of_nonneg_left hfin (show (0:ℝ) ≤ (s:ℝ)+1 by positivity)
        have hs₂ := mul_le_mul_of_nonneg_right hC hn'
        nlinarith only [ih hc' hb h htb, hmul, hm, hs₁, hs₂]
      · subst t
        have hfin := sqrt_step hp hq (le_refl (0:ℝ)) hp.le
        have he : (x n-a)+(b-x n)=b-a := by ring
        rw [Real.sqrt_zero, zero_mul, zero_add, sub_zero, he, mul_comm (b-x n)] at hfin
        apply birth.trans (hfin.trans _)
        simpa using mul_le_mul_of_nonneg_right hC
          (mul_nonneg (Real.sqrt_nonneg (x n-a)) (Real.sqrt_nonneg (b-x n)))
      · have hac := ne_of_gt (sub_pos.mpr hc.1)
        have hsplit : chord x (n+1) a t b = chord x (n+1) a t (x n) +
            (t-a)/(x n-a)*chord x (n+1) a (x n) b := by
          unfold chord
          field_simp [hn,hac]
          ring
        have hm := mul_le_mul_of_nonneg_left birth
          (div_nonneg hp.le (sub_nonneg.mpr hc.1.le))
        have he : (t-a)/(x n-a)*((x n-a)*(b-x n)/(b-a)) =
            (t-a)*((b-t)-(x n-t))/((b-t)+(t-a)) := by
          rw [show (b-t)+(t-a)=b-a by ring]
          field_simp [hn,hac]
          ring
        rw [he] at hm
        rw [hsplit, chord_outside x n hat h (Or.inr le_rfl)]
        have hfin := sqrt_step hq hp (sub_nonneg.mpr h.le) (by linarith : x n-t ≤ b-t)
        rw [mul_comm (Real.sqrt (x n-t)), mul_comm (Real.sqrt (b-t))] at hfin
        have hmul := mul_nonneg hp.le (sub_nonneg.mpr h.le)
        have hn' : 0 ≤ (t-a)*((b-t)-(x n-t))/((b-t)+(t-a)) :=
          div_nonneg (mul_nonneg hp.le (by linarith [hc.2])) (add_pos hq hp).le
        have hs₁ := mul_le_mul_of_nonneg_left hfin (show (0:ℝ) ≤ (s:ℝ)+1 by positivity)
        have hs₂ := mul_le_mul_of_nonneg_right hC hn'
        nlinarith only [ih ha hc' hat h, hmul, hm, hs₁, hs₂]
    · have ho : x n ≤ a ∨ b ≤ x n := by
        by_cases h : x n ≤ a
        · exact Or.inl h
        · exact Or.inr (le_of_not_gt fun h' => hc ⟨lt_of_not_ge h,h'⟩)
      rw [chord_outside x n hat htb ho]
      linarith [ih ha hb hat htb, mul_nonneg hp.le hq.le]


theorem integrated_discrepancy_from_seed {x : Seq} {s N : ℕ} (g : GreedyFrom x s)
    (hs : s ≤ N) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    |∫ u in (0:ℝ)..t, D x N u| ≤ seedBound s + ((s:ℝ)+1)/2 := by
  rw [primitive_eq_integral (fun i => (g.1 i).1) N ht.1]
  have h0 := H_zero_of_unit g.1 N
  have z0 : (0:ℝ) ∈ Set.Icc 0 1 := by constructor <;> norm_num
  have z1 : (1:ℝ) ∈ Set.Icc 0 1 := by constructor <;> norm_num
  have hb0 : 0 ≤ seedBound s := (by norm_num : (0:ℝ) ≤ 1/2).trans (le_max_left _ _)
  have hseed : (0:ℝ) ≤ (s:ℝ)+1 := by positivity
  have htop := boundary_from g hs ht
  have htop' := mul_le_mul_of_nonneg_left ht.2 hb0
  apply abs_le.mpr
  refine ⟨?_, by nlinarith⟩
  have hbot := boundary_from (reflect_from g) hs z1
  rw [H_reflect_of_unit g.1, sub_self, h0, zero_sub, mul_one] at hbot
  rcases eq_or_lt_of_le ht.1 with h | hp
  · rw [← h, h0]
    nlinarith
  rcases eq_or_lt_of_le ht.2 with h | hq
  · rw [h]
    nlinarith
  have hch := chord_from_seed g hs z0 z1 hp hq
  simp [chord,h0] at hch
  have hAM : Real.sqrt t * Real.sqrt (1-t) ≤ 1/2 := by
    have h₁ := Real.sq_sqrt ht.1
    have h₂ := Real.sq_sqrt (sub_nonneg.mpr ht.2)
    nlinarith [sq_nonneg (Real.sqrt t-Real.sqrt (1-t))]
  have hm := mul_le_mul_of_nonneg_left hAM (show (0:ℝ) ≤ (s:ℝ)+1 by positivity)
  have hm' := mul_le_mul_of_nonneg_left hbot ht.1
  nlinarith

#print axioms star_discrepancy_from_seed
#print axioms chord_from_seed
#print axioms integrated_discrepancy_from_seed
end
end Kritzinger
