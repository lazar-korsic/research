import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace Kritzinger
open Finset
noncomputable section

abbrev Seq := ℕ → ℝ

def H (x : Seq) (n : ℕ) (t : ℝ) : ℝ :=
  (∑ i ∈ range n, max 0 (t - x i)) - (n : ℝ) * t^2 / 2

def D (x : Seq) (n : ℕ) (t : ℝ) : ℝ :=
  (∑ i ∈ range n, if x i < t then (1 : ℝ) else 0) - (n : ℝ) * t

def K (x : Seq) (n : ℕ) (t : ℝ) := H x n t + t*(1-t)/2

def Greedy (x : Seq) : Prop :=
  (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) ∧
  ∀ n t, t ∈ Set.Icc (0 : ℝ) 1 → K x n t ≤ K x n (x n)

theorem H_succ (x : Seq) (n : ℕ) (t : ℝ) :
    H x (n+1) t = H x n t + max 0 (t - x n) - t^2/2 := by
  simp only [H, sum_range_succ, Nat.cast_add, Nat.cast_one]
  ring

theorem D_succ (x : Seq) (n : ℕ) (t : ℝ) :
    D x (n+1) t = D x n t + (if x n < t then 1 else 0) - t := by
  simp only [D, sum_range_succ, Nat.cast_add, Nat.cast_one]
  ring

theorem cone_step {x : Seq} (n : ℕ) (g : ∀ u ∈ Set.Icc (0:ℝ) 1, K x n u ≤ K x n (x n)) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) :
    H x (n+1) t - H x (n+1) (x n) ≤ |t-x n|/2 := by
  have h := g t ht
  unfold K at h
  rw [H_succ, H_succ, sub_self, max_self, abs_eq_max_neg]
  rcases le_total 0 (t-x n) with hp | hp
  · rw [max_eq_right hp, max_eq_left (by linarith : -(t-x n) ≤ t-x n)]
    nlinarith
  · rw [max_eq_left hp, max_eq_right (by linarith : t-x n ≤ -(t-x n))]
    nlinarith

theorem cone {x : Seq} (g : Greedy x) (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) :
    H x (n+1) t - H x (n+1) (x n) ≤ |t-x n|/2 := cone_step n (g.2 n) ht

theorem boundary {x : Seq} (g : Greedy x) (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) : H x n t ≤ t/2 := by
  induction n generalizing t with
  | zero => simpa [H] using (show 0 ≤ t/2 by linarith [ht.1])
  | succ n ih =>
    rcases le_total t (x n) with h | h
    · rw [H_succ, max_eq_left (sub_nonpos.mpr h)]
      nlinarith [ih ht, sq_nonneg t]
    · have hc := cone g n ht
      rw [abs_of_nonneg (sub_nonneg.mpr h), H_succ x n (x n), sub_self, max_self] at hc
      nlinarith [ih (g.1 n), sq_nonneg (x n)]

def S (x : Seq) (n : ℕ) (a t : ℝ) := (H x n t - H x n a)/(t-a)
def R (x : Seq) (n : ℕ) (a t : ℝ) := D x n t - S x n a t

theorem outside (x : Seq) (n : ℕ) {a t : ℝ} (hat : a < t)
    (hc : x n ≤ a ∨ t ≤ x n) :
    R x (n+1) a t = R x n a t - (t-a)/2 := by
  unfold R S
  rw [D_succ, H_succ, H_succ]
  rcases hc with h | h
  · rw [if_pos (lt_of_le_of_lt h hat), max_eq_right (by linarith : 0 ≤ t-x n),
      max_eq_right (sub_nonneg.mpr h)]
    field_simp [ne_of_gt (sub_pos.mpr hat)]
    ring
  · rw [if_neg (not_lt.mpr h), max_eq_left (sub_nonpos.mpr h),
      max_eq_left (by linarith : a-x n ≤ 0)]
    field_simp [ne_of_gt (sub_pos.mpr hat)]
    ring

theorem inside_step {x : Seq} (n : ℕ) (g : ∀ u ∈ Set.Icc (0:ℝ) 1, K x n u ≤ K x n (x n)) {a t : ℝ}
    (ha : a ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hac : a < x n) (hct : x n < t) :
    R x (n+1) a t ≤ R x n (x n) t - (t-x n)/2 + (1-(t-x n)/(t-a)) := by
  have ca := cone_step n g ha
  have ct := cone_step n g ht
  rw [abs_of_neg (sub_neg.mpr hac)] at ca
  rw [abs_of_pos (sub_pos.mpr hct)] at ct
  have L : -(1/2:ℝ) ≤ S x (n+1) a (x n) := by
    unfold S
    apply (le_div_iff₀ (sub_pos.mpr hac)).2
    linarith
  have U : S x (n+1) (x n) t ≤ 1/2 := by
    unfold S
    apply (div_le_iff₀ (sub_pos.mpr hct)).2
    linarith
  have e : S x (n+1) (x n) t - S x (n+1) a t =
      ((x n-a)/(t-a))*(S x (n+1) (x n) t - S x (n+1) a (x n)) := by
    unfold S
    field_simp [ne_of_gt (sub_pos.mpr hac), ne_of_gt (sub_pos.mpr hct),
      ne_of_gt (sub_pos.mpr (hac.trans hct))]
    ring
  have h := mul_le_mul_of_nonneg_left (show S x (n+1) (x n) t - S x (n+1) a (x n) ≤ 1 by linarith)
      (div_nonneg (sub_nonneg.mpr hac.le) (sub_nonneg.mpr (hac.trans hct).le))
  rw [← e, mul_one] at h
  have er : (x n-a)/(t-a) = 1-(t-x n)/(t-a) := by
    field_simp [ne_of_gt (sub_pos.mpr (hac.trans hct))]
  rw [er] at h
  have ho := outside x n hct (Or.inl le_rfl)
  unfold R at *
  linarith

theorem inside {x : Seq} (g : Greedy x) (n : ℕ) {a t : ℝ}
    (ha : a ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hac : a < x n) (hct : x n < t) :
    R x (n+1) a t ≤ R x n (x n) t - (t-x n)/2 + (1-(t-x n)/(t-a)) := inside_step n (g.2 n) ha ht hac hct

theorem empty_interval (x : Seq) (n : ℕ) {a t : ℝ} (hat : a < t)
    (he : ∀ i < n, ¬ (a < x i ∧ x i < t)) : R x n a t ≤ 0 := by
  induction n with
  | zero => simp [R, D, S, H]
  | succ n ih =>
    have h := he n (by omega)
    have ho : x n ≤ a ∨ t ≤ x n := by
      by_cases h' : x n ≤ a
      · exact Or.inl h'
      · exact Or.inr (le_of_not_gt fun h'' => h ⟨lt_of_not_ge h', h''⟩)
    rw [outside x n hat ho]
    linarith [ih (fun i hi => he i (by omega))]


def quad (x : Seq) (n : ℕ) (s : Finset ℕ) (t : ℝ) :=
  ((s.card : ℝ)+1/2)*t - ∑ i ∈ s, x i - ((n:ℝ)+1)*t^2/2

theorem quad_le (x : Seq) (n : ℕ) {s : Finset ℕ} (hs : s ⊆ range n) (t : ℝ) :
    quad x n s t ≤ K x n t := by
  have h₁ : (∑ i ∈ s, (t-x i)) ≤ ∑ i ∈ s, max 0 (t-x i) :=
    sum_le_sum fun _ _ => le_max_right _ _
  have h₂ : (∑ i ∈ s, max 0 (t-x i)) ≤ ∑ i ∈ range n, max 0 (t-x i) :=
    sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => le_max_left _ _)
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul] at h₁
  unfold quad K H
  linarith

theorem quad_touch (x : Seq) (n : ℕ) (t : ℝ) :
    quad x n ((range n).filter (fun i => x i < t)) t = K x n t := by
  classical
  have e : (∑ i ∈ range n, max 0 (t-x i)) =
      ∑ i ∈ (range n).filter (fun i => x i < t), (t-x i) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro i _
    split_ifs with h
    · exact max_eq_right (sub_nonneg.mpr h.le)
    · exact max_eq_left (sub_nonpos.mpr (not_lt.mp h))
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul] at e
  unfold quad K H
  rw [e]
  ring

def vertex (n : ℕ) (s : Finset ℕ) : ℝ := ((s.card : ℝ)+1/2)/((n:ℝ)+1)

theorem vertex_mem {n : ℕ} {s : Finset ℕ} (hs : s ⊆ range n) :
    vertex n s ∈ Set.Icc (0:ℝ) 1 := by
  have h : (s.card : ℝ) ≤ n := by exact_mod_cast (card_le_card hs).trans_eq (card_range n)
  unfold vertex
  have hn : (0:ℝ) < (n:ℝ)+1 := by positivity
  exact ⟨by positivity, (div_le_one hn).2 (by linarith)⟩

theorem vertex_diff (x : Seq) (n : ℕ) (s : Finset ℕ) (t : ℝ) :
    quad x n s (vertex n s) - quad x n s t =
      ((n:ℝ)+1)/2 * (vertex n s-t)^2 := by
  have e : ((n:ℝ)+1)*vertex n s = (s.card:ℝ)+1/2 := by
    unfold vertex
    field_simp; ring
  unfold quad
  linear_combination -(vertex n s-t) * e

theorem separation_step {x : Seq} {i n : ℕ} (g : ∀ u ∈ Set.Icc (0:ℝ) 1, K x n u ≤ K x n (x n)) (hi : i < n) :
    1/(2*((n:ℝ)+1)) ≤ |x n-x i| := by
  classical
  let s := (range n).filter (fun j => x j < x n)
  have hs : s ⊆ range n := filter_subset _ _
  have touch : quad x n s (x n) = K x n (x n) := quad_touch x n (x n)
  have hb (u : Finset ℕ) (hu : u ⊆ range n) :
      quad x n u (vertex n u) ≤ quad x n s (x n) :=
    (quad_le x n hu _).trans ((g _ (vertex_mem hu)).trans_eq touch.symm)
  have hn : (0:ℝ) < (n:ℝ)+1 := by positivity
  have hv : vertex n s = x n := by
    have h := hb s hs
    have e := vertex_diff x n s (x n)
    by_contra hne
    have hpos := mul_pos (half_pos hn) (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))
    linarith
  by_cases h : x i < x n
  · have his : i ∈ s := mem_filter.mpr ⟨mem_range.mpr hi, h⟩
    have hu : s.erase i ⊆ range n := (erase_subset _ _).trans hs
    have hc : ((s.erase i).card : ℝ) + 1 = s.card := by
      exact_mod_cast (card_erase_add_one his)
    have hsum : (∑ j ∈ s.erase i, x j) + x i = ∑ j ∈ s, x j := sum_erase_add _ _ his
    have ve : vertex n (s.erase i) - x n = -1/((n:ℝ)+1) := by
      rw [← hv]
      unfold vertex
      rw [div_sub_div_same]
      congr 1
      linarith
    have e := vertex_diff x n (s.erase i) (x n)
    rw [ve] at e
    have hh := hb (s.erase i) hu
    have q : quad x n (s.erase i) (x n) - quad x n s (x n) = x i-x n := by
      unfold quad
      linear_combination x n * hc - hsum
    have k : ((n:ℝ)+1)/2 * (-1/((n:ℝ)+1))^2 = 1/(2*((n:ℝ)+1)) := by
      field_simp
      ring
    rw [k] at e
    rw [abs_of_pos (sub_pos.mpr h)]
    linarith
  · have his : i ∉ s := fun hm => h (mem_filter.mp hm).2
    have hu : insert i s ⊆ range n := insert_subset (mem_range.mpr hi) hs
    have hc : ((insert i s).card : ℝ) = s.card + 1 := by rw [card_insert_of_not_mem his]; push_cast; rfl
    have ve : vertex n (insert i s) - x n = 1/((n:ℝ)+1) := by
      rw [← hv]
      unfold vertex
      rw [div_sub_div_same]
      congr 1
      linarith
    have e := vertex_diff x n (insert i s) (x n)
    rw [ve] at e
    have hh := hb (insert i s) hu
    have q : quad x n (insert i s) (x n) - quad x n s (x n) = x n-x i := by
      unfold quad
      rw [sum_insert his]
      linear_combination x n * hc
    have k : ((n:ℝ)+1)/2 * (1/((n:ℝ)+1))^2 = 1/(2*((n:ℝ)+1)) := by
      field_simp
      ring
    rw [k] at e
    rw [abs_of_nonpos (sub_nonpos.mpr (not_lt.mp h))]
    linarith

theorem separation {x : Seq} (g : Greedy x) {i n : ℕ} (hi : i < n) :
    1/(2*((n:ℝ)+1)) ≤ |x n-x i| := separation_step (g.2 n) hi

theorem trace {x : Seq} (g : Greedy x) {N : ℕ} (hN : 0 < N)
    {n : ℕ} (hn : n ≤ N) {a t : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hat : a < t) :
    R x n a t ≤ 1 + max 0 (Real.log (2*(N:ℝ)*(t-a))) := by
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  induction n generalizing a with
  | zero =>
    have hh := le_max_left 0 (Real.log (2*(N:ℝ)*(t-a)))
    simp [R, D, S, H]
    linarith
  | succ n ih =>
    have hn' : n ≤ N := by omega
    by_cases hc : a < x n ∧ x n < t
    · have e := inside g n ha ht hc.1 hc.2
      have hh := sub_pos.mpr hc.2
      by_cases hshort : 2*(N:ℝ)*(t-x n) < 1
      · have he : ∀ i < n, ¬ (x n < x i ∧ x i < t) := by
          intro i hi h
          have hs := separation g hi
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


theorem upper {x : Seq} (g : Greedy x) {N : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    D x N t ≤ Real.log (2*(N:ℝ)) + 3/2 := by
  have hNp : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (2*(N:ℝ)) := Real.log_nonneg (by linarith)
  rcases eq_or_lt_of_le ht.1 with he | hp
  · subst t
    have hz : (∑ i ∈ range N, if x i < 0 then (1:ℝ) else 0) = 0 :=
      sum_eq_zero fun i _ => if_neg (not_lt.mpr (g.1 i).1)
    simp [D, hz]
    linarith
  have h := trace g hN le_rfl (by constructor <;> norm_num : (0:ℝ) ∈ Set.Icc 0 1) ht hp
  have H0 : H x N 0 = 0 := by
    have hz : (∑ i ∈ range N, max 0 ((0:ℝ)-x i)) = 0 :=
      sum_eq_zero fun i _ => max_eq_left (by linarith [(g.1 i).1])
    simp only [H, hz]
    ring
  have hm : S x N 0 t ≤ 1/2 := by
    unfold S
    rw [H0, sub_zero, sub_zero]
    exact (div_le_iff₀ hp).2 (by linarith [boundary g N ht])
  have hl : Real.log (2*(N:ℝ)*t) ≤ Real.log (2*(N:ℝ)) :=
    Real.log_le_log (by positivity) (by
      simpa using mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ 2*(N:ℝ) by positivity))
  simp only [sub_zero] at h
  have hh := max_le hlog hl
  unfold R at h
  linarith

def reflect (x : Seq) : Seq := fun i => 1-x i

theorem H_reflect_of_unit {x : Seq} (hx : ∀ i, x i ∈ Set.Icc (0:ℝ) 1) (n : ℕ) (t : ℝ) :
    H (reflect x) n t = H x n (1-t) - H x n 1 := by
  induction n with
  | zero => simp [H]
  | succ n ih =>
    rw [H_succ, H_succ, H_succ, ih, reflect,
      max_eq_right (by linarith [(hx n).2] : 0 ≤ 1-x n)]
    rcases le_total (x n) (1-t) with hh | hh
    · rw [max_eq_left (by linarith : t-(1-x n) ≤ 0), max_eq_right (sub_nonneg.mpr hh)]
      ring
    · rw [max_eq_right (by linarith : 0 ≤ t-(1-x n)), max_eq_left (sub_nonpos.mpr hh)]
      ring

theorem H_reflect {x : Seq} (g : Greedy x) (n : ℕ) (t : ℝ) :
    H (reflect x) n t = H x n (1-t) - H x n 1 := H_reflect_of_unit g.1 n t

theorem greedy_reflect {x : Seq} (g : Greedy x) : Greedy (reflect x) := by
  constructor
  · intro i
    have hi := g.1 i
    change 0 ≤ 1-x i ∧ 1-x i ≤ 1
    constructor <;> linarith [hi.1, hi.2]
  · intro n t ht
    have h := g.2 n (1-t) (by constructor <;> linarith [ht.1, ht.2])
    unfold K at *
    rw [H_reflect g, H_reflect g]
    unfold reflect
    rw [sub_sub_cancel] 
    nlinarith

theorem abs_of_reflected_upper {x : Seq} (hx : ∀ i, x i ∈ Set.Icc (0:ℝ) 1) {N : ℕ} (hN : 0 < N)
    {B : ℝ} (hB : 0 ≤ B)
    (up : ∀ u ∈ Set.Icc (0:ℝ) 1, D x N u ≤ B)
    (ur : ∀ u ∈ Set.Icc (0:ℝ) 1, D (reflect x) N u ≤ B)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    |D x N t| ≤ B := by
  apply abs_le.mpr
  refine ⟨?_, up t ht⟩
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  rcases eq_or_lt_of_le ht.1 with ho | hp
  · subst t
    have hz : (∑ i ∈ range N, if x i < 0 then (1:ℝ) else 0) = 0 :=
      sum_eq_zero fun i _ => if_neg (not_lt.mpr (hx i).1)
    simp [D, hz]
    linarith
  change -B ≤ D x N t
  by_contra! hh
  let e := min t ((-B-D x N t)/(2*(N:ℝ)))
  have ep : 0 < e := lt_min hp (div_pos (sub_pos.mpr hh) (by positivity))
  have el : e ≤ t := min_le_left _ _
  have eb : e * (2*(N:ℝ)) ≤ -B-D x N t :=
    (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  let u := 1-t+e
  have hu : u ∈ Set.Icc (0:ℝ) 1 := by constructor <;> dsimp [u] <;> linarith [ht.2]
  have hU := ur u hu
  change D (reflect x) N u ≤ B at hU
  have hs : (∑ i ∈ range N, (1-(if x i < t then (1:ℝ) else 0))) ≤
      ∑ i ∈ range N, if reflect x i < u then (1:ℝ) else 0 := by
    apply sum_le_sum
    intro i _
    by_cases hi : x i < t
    · rw [if_pos hi, sub_self]
      split_ifs <;> norm_num
    · rw [if_neg hi, if_pos (show reflect x i < u by dsimp [reflect, u]; linarith [le_of_not_gt hi])]
      norm_num
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, card_range, mul_one] at hs
  unfold D at hU eb
  dsimp [u] at hU
  nlinarith


theorem star_discrepancy {x : Seq} (g : Greedy x) {N : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    |D x N t| ≤ Real.log (2*(N:ℝ)) + 3/2 := by
  apply abs_of_reflected_upper g.1 hN ?_ (fun _ => upper g hN)
    (fun _ => upper (greedy_reflect g) hN) ht
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  linarith [Real.log_nonneg (show 1 ≤ 2*(N:ℝ) by linarith)]

/-- Equation (1) of the paper, with zero-based indices for the old points. -/
def objective (x : Seq) (n : ℕ) (t : ℝ) :=
  ((n:ℝ)+1)*t^2-t-2* ∑ i ∈ range n, max t (x i)

theorem objective_eq (x : Seq) (n : ℕ) (t : ℝ) :
    objective x n t = -2*K x n t - 2* ∑ i ∈ range n, x i := by
  have e : (∑ i ∈ range n, max t (x i)) =
      ∑ i ∈ range n, (max 0 (t-x i) + x i) := by
    apply sum_congr rfl
    intro i _
    rcases le_total t (x i) with h | h
    · rw [max_eq_right h, max_eq_left (sub_nonpos.mpr h), zero_add]
    · rw [max_eq_left h, max_eq_right (sub_nonneg.mpr h)]
      ring
  rw [sum_add_distrib] at e
  unfold objective K H
  rw [e]
  ring

theorem star_discrepancy_from_objective {x : Seq}
    (hx : ∀ i, x i ∈ Set.Icc (0:ℝ) 1)
    (hg : ∀ n t, t ∈ Set.Icc (0:ℝ) 1 → objective x n (x n) ≤ objective x n t)
    {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    |D x N t| ≤ Real.log (2*(N:ℝ)) + 3/2 := by
  apply star_discrepancy ⟨hx, ?_⟩ hN ht
  intro n u hu
  have h := hg n u hu
  simp only [objective_eq] at h
  linarith

def chord (x : Seq) (n : ℕ) (a t b : ℝ) :=
  ((b-t)*H x n a + (t-a)*H x n b)/(b-a) - H x n t

theorem chord_outside (x : Seq) (n : ℕ) {a t b : ℝ} (hat : a < t) (htb : t < b)
    (hc : x n ≤ a ∨ b ≤ x n) :
    chord x (n+1) a t b = chord x n a t b - (t-a)*(b-t)/2 := by
  have hn := ne_of_gt (sub_pos.mpr (hat.trans htb))
  unfold chord
  simp only [H_succ]
  rcases hc with h | h
  · rw [max_eq_right (sub_nonneg.mpr h),
      max_eq_right (by linarith : 0 ≤ b-x n), max_eq_right (by linarith : 0 ≤ t-x n)]
    field_simp [hn]
    ring
  · rw [max_eq_left (sub_nonpos.mpr h),
      max_eq_left (by linarith : a-x n ≤ 0), max_eq_left (by linarith : t-x n ≤ 0)]
    field_simp [hn]
    ring

theorem chord_birth_step {x : Seq} (n : ℕ) (g : ∀ u ∈ Set.Icc (0:ℝ) 1, K x n u ≤ K x n (x n)) {a b : ℝ}
    (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1)
    (hac : a < x n) (hcb : x n < b) :
    chord x (n+1) a (x n) b ≤ (x n-a)*(b-x n)/(b-a) := by
  have ca := cone_step n g ha
  have cb := cone_step n g hb
  rw [abs_of_neg (sub_neg.mpr hac)] at ca
  rw [abs_of_pos (sub_pos.mpr hcb)] at cb
  unfold chord
  rw [div_sub' (ne_of_gt (sub_pos.mpr (hac.trans hcb)))]
  apply (div_le_div_iff_of_pos_right (sub_pos.mpr (hac.trans hcb))).2
  nlinarith [mul_le_mul_of_nonneg_left ca (sub_nonneg.mpr hcb.le),
    mul_le_mul_of_nonneg_left cb (sub_nonneg.mpr hac.le)]

theorem chord_birth {x : Seq} (g : Greedy x) (n : ℕ) {a b : ℝ}
    (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1)
    (hac : a < x n) (hcb : x n < b) :
    chord x (n+1) a (x n) b ≤ (x n-a)*(b-x n)/(b-a) := chord_birth_step n (g.2 n) ha hb hac hcb

theorem sqrt_step {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 ≤ r) (hrp : r ≤ p) :
    Real.sqrt r * Real.sqrt q + q*(p-r)/(p+q) ≤ Real.sqrt p * Real.sqrt q := by
  have er := Real.sq_sqrt hr
  have ep := Real.sq_sqrt hp.le
  have eq := Real.sq_sqrt hq.le
  have sp := Real.sqrt_pos.2 hp
  have sq := Real.sqrt_pos.2 hq
  have sr := Real.sqrt_nonneg r
  have e₁ : 2 * Real.sqrt p * Real.sqrt q ≤ p+q := by
    nlinarith [sq_nonneg (Real.sqrt p - Real.sqrt q)]
  have e₂ : p-r ≤ 2*Real.sqrt p*(Real.sqrt p-Real.sqrt r) := by
    nlinarith [sq_nonneg (Real.sqrt p - Real.sqrt r)]
  have e₃ := mul_le_mul_of_nonneg_left e₁ (sub_nonneg.mpr (Real.sqrt_le_sqrt hrp))
  have e₄ := mul_le_mul_of_nonneg_left e₂ (Real.sqrt_nonneg q)
  rw [add_comm, ← le_sub_iff_add_le]
  apply (div_le_iff₀ (add_pos hp hq)).2
  have e₅ := mul_le_mul_of_nonneg_left (e₄.trans (show
    Real.sqrt q * (2 * Real.sqrt p * (Real.sqrt p - Real.sqrt r)) ≤
    (p+q)*(Real.sqrt p-Real.sqrt r) by nlinarith only [e₃])) (Real.sqrt_nonneg q)
  calc
    q*(p-r) = Real.sqrt q * (Real.sqrt q * (p-r)) := by rw [← mul_assoc, ← pow_two, eq]
    _ ≤ Real.sqrt q * ((p+q)*(Real.sqrt p-Real.sqrt r)) := e₅
    _ = (Real.sqrt p * Real.sqrt q - Real.sqrt r * Real.sqrt q)*(p+q) := by ring

theorem chord_bound {x : Seq} (g : Greedy x) (n : ℕ) {a t b : ℝ}
    (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1)
    (hat : a < t) (htb : t < b) :
    chord x n a t b ≤ Real.sqrt (t-a)*Real.sqrt (b-t) := by
  induction n generalizing a t b with
  | zero => simp [chord,H]; positivity
  | succ n ih =>
    have hp := sub_pos.mpr hat
    have hq := sub_pos.mpr htb
    have hn := ne_of_gt (sub_pos.mpr (hat.trans htb))
    by_cases hc : a < x n ∧ x n < b
    · have hc' := g.1 n
      have birth := chord_birth g n ha hb hc.1 hc.2
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
        linarith [ih hc' hb h htb]
      · subst t
        have hfin := sqrt_step hp hq (le_refl (0:ℝ)) hp.le
        have he : (x n-a)+(b-x n)=b-a := by ring
        rw [Real.sqrt_zero, zero_mul, zero_add, sub_zero, he, mul_comm (b-x n)] at hfin
        exact birth.trans hfin
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
        linarith [ih ha hc' hat h]
    · have ho : x n ≤ a ∨ b ≤ x n := by
        by_cases h : x n ≤ a
        · exact Or.inl h
        · exact Or.inr (le_of_not_gt fun h' => hc ⟨lt_of_not_ge h,h'⟩)
      rw [chord_outside x n hat htb ho]
      linarith [ih ha hb hat htb, mul_nonneg hp.le hq.le]


theorem H_zero {x : Seq} (g : Greedy x) (N : ℕ) : H x N 0 = 0 := by
  have hz : (∑ i ∈ range N, max 0 ((0:ℝ)-x i)) = 0 :=
    sum_eq_zero fun i _ => max_eq_left (by linarith [(g.1 i).1])
  simp only [H,hz]
  ring

theorem primitive_bound {x : Seq} (g : Greedy x) (N : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) : |H x N t| ≤ (1+Real.sqrt 5)/4 := by
  have ht0 := ht.1
  have ht1 := ht.2
  have lo : -(1/2:ℝ) ≤ H x N 1 := by
    have hh := boundary (greedy_reflect g) N (show (1:ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    rw [H_reflect g, sub_self, H_zero g N] at hh
    linarith
  have hs5 := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have hs5' := Real.sqrt_nonneg (5:ℝ)
  have h1 : 1 ≤ Real.sqrt (5:ℝ) := by nlinarith
  apply abs_le.mpr
  refine ⟨?_, by linarith [boundary g N ht]⟩
  rcases eq_or_lt_of_le ht0 with he | hp
  · rw [← he, H_zero g N]
    linarith
  rcases eq_or_lt_of_le ht1 with he | hq
  · rw [he]
    linarith
  have z := chord_bound g N
      (show (0:ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
      (show (1:ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num) hp hq
  simp [chord,H_zero g N] at z
  let s := Real.sqrt t * Real.sqrt (1-t)
  have hs : s^2 = t*(1-t) := by
    dsimp [s]
    rw [mul_pow, Real.sq_sqrt ht0, Real.sq_sqrt (sub_nonneg.mpr ht1)]
  have hu : (2*t-1+4*s)^2 ≤ 5 := by
    nlinarith [sq_nonneg (2*(2*t-1)-2*s)]
  have hu' : 2*t-1+4*s ≤ Real.sqrt 5 := by
    by_contra! hh
    have hdiff : 0 < 2*t-1+4*s-Real.sqrt 5 := sub_pos.mpr hh
    have hsum : 0 < 2*t-1+4*s+Real.sqrt 5 := by linarith
    have hp' := mul_pos hdiff hsum
    nlinarith only [hu, hp', hs5]
  have hmul := mul_le_mul_of_nonneg_left lo ht0
  change t * H x N 1 ≤ s + H x N t at z
  linarith

theorem midpoint_bound {x : Seq} (g : Greedy x) (N : ℕ)
    {a b : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1) (hab : a < b) :
    (H x N a - 2*H x N ((a+b)/2) + H x N b)/(b-a) ≤ 1 := by
  have h := chord_bound g N ha hb (show a < (a+b)/2 by linarith)
    (show (a+b)/2 < b by linarith)
  rw [show b-(a+b)/2=(a+b)/2-a by ring, ← pow_two,
    Real.sq_sqrt (by linarith : 0 ≤ (a+b)/2-a)] at h
  unfold chord at h
  have hp := sub_pos.mpr hab
  have he : 0 < (b-a)^2 := sq_pos_of_pos hp
  apply (div_le_iff₀ hp).2
  rw [one_mul]
  have h' := (div_le_iff₀ hp).1 (sub_le_iff_le_add.mp h)
  -- Both expressions for the chord at a midpoint have the same value.
  have hm : (b-(a+b)/2)*H x N a + ((a+b)/2-a)*H x N b =
      (b-a)*((H x N a + H x N b)/2) := by ring
  rw [hm] at h'
  have hv : (H x N a + H x N b)/2 ≤ (a+b)/2-a + H x N ((a+b)/2) := by
    apply (le_of_mul_le_mul_left ?_ hp)
    simpa only [mul_comm (b-a)] using h'
  linarith


open MeasureTheory

theorem step_integrable (c a b : ℝ) :
    IntervalIntegrable (fun u => if c < u then (1:ℝ) else 0) volume a b := by
  rw [intervalIntegrable_iff]
  have h := (intervalIntegrable_iff.mp
    (show IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume a b from intervalIntegrable_const))
    |>.indicator (t := Set.Ioi c) measurableSet_Ioi
  simpa only [Set.indicator, Set.mem_Ioi] using h

theorem step_integral {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    (∫ u in (0:ℝ)..t, if c < u then (1:ℝ) else 0) = max 0 (t-c) := by
  change (∫ u in (0:ℝ)..t, (Set.Ioi c).indicator (fun _ => (1:ℝ)) u) = _
  rw [intervalIntegral.integral_of_le ht, MeasureTheory.integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi]
  have he : Set.Ioi c ∩ Set.Ioc 0 t = Set.Ioc c t := by
    ext u
    constructor
    · exact fun h => ⟨h.1,h.2.2⟩
    · exact fun h => ⟨h.1, hc.trans_lt h.1, h.2⟩
  rw [he, MeasureTheory.integral_const, Measure.real_def, Measure.restrict_apply_univ, Real.volume_Ioc, ENNReal.toReal_ofReal', smul_eq_mul,
    mul_one]
  exact max_comm _ _

theorem primitive_eq_integral {x : Seq} (hx : ∀ i, 0 ≤ x i)
    (N : ℕ) {t : ℝ} (ht : 0 ≤ t) : (∫ u in (0:ℝ)..t, D x N u) = H x N t := by
  let f (i : ℕ) (u : ℝ) := if x i < u then (1:ℝ) else 0
  change (∫ u in (0:ℝ)..t, (∑ i ∈ range N, f i u) - (N:ℝ)*u) = _
  have hf : ∀ i ∈ range N, IntervalIntegrable (f i) volume 0 t :=
    fun i _ => step_integrable (x i) 0 t
  have hg : IntervalIntegrable (fun u : ℝ => (N:ℝ)*u) volume 0 t :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  simp_rw [← Finset.sum_apply]
  rw [intervalIntegral.integral_sub (IntervalIntegrable.sum _ hf) hg]
  simp_rw [Finset.sum_apply]
  rw [intervalIntegral.integral_finset_sum hf, intervalIntegral.integral_const_mul, integral_id]
  unfold H
  congr 1
  · exact sum_congr rfl fun i _ => step_integral (hx i) ht
  · ring

theorem integrated_discrepancy {x : Seq} (g : Greedy x) (N : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) :
    |∫ u in (0:ℝ)..t, D x N u| ≤ (1+Real.sqrt 5)/4 := by
  rw [primitive_eq_integral (fun i => (g.1 i).1) N ht.1]
  exact primitive_bound g N ht


def tent (a b y : ℝ) := max 0 (min (y-a) (b-y))/(b-a)

theorem tent_numerator {a b : ℝ} (hab : a < b) (y : ℝ) :
    max 0 (a-y) - 2*max 0 ((a+b)/2-y) + max 0 (b-y) =
    max 0 (min (y-a) (b-y)) := by
  rcases le_or_gt y a with h | h
  · rw [max_eq_right (by linarith : 0 ≤ a-y), max_eq_right (by linarith : 0 ≤ (a+b)/2-y),
      max_eq_right (by linarith : 0 ≤ b-y), min_eq_left (by linarith : y-a ≤ b-y),
      max_eq_left (by linarith : y-a ≤ 0)]
    ring
  rcases le_or_gt y ((a+b)/2) with h' | h'
  · rw [max_eq_left (by linarith : a-y ≤ 0), max_eq_right (sub_nonneg.mpr h'),
      max_eq_right (by linarith : 0 ≤ b-y), min_eq_left (by linarith : y-a ≤ b-y),
      max_eq_right (by linarith : 0 ≤ y-a)]
    ring
  rcases le_or_gt y b with h'' | h''
  · rw [max_eq_left (by linarith : a-y ≤ 0), max_eq_left (by linarith : (a+b)/2-y ≤ 0),
      max_eq_right (sub_nonneg.mpr h''), min_eq_right (by linarith : b-y ≤ y-a),
      max_eq_right (sub_nonneg.mpr h'')]
    ring
  · rw [max_eq_left (by linarith : a-y ≤ 0), max_eq_left (by linarith : (a+b)/2-y ≤ 0),
      max_eq_left (by linarith : b-y ≤ 0), min_eq_right (by linarith : b-y ≤ y-a),
      max_eq_left (by linarith : b-y ≤ 0)]
    ring

theorem tent_bound {x : Seq} (g : Greedy x) (N : ℕ)
    {a b : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1) (hab : a < b) :
    (∑ i ∈ range N, tent a b (x i)) - (N:ℝ)*(b-a)/4 ≤ 1 := by
  have hn := ne_of_gt (sub_pos.mpr hab)
  have h := midpoint_bound g N ha hb hab
  unfold H at h
  unfold tent
  simp only [← sum_div, ← sum_add_distrib, ← mul_sum, ← sum_sub_distrib,
    ← tent_numerator hab] at *
  apply (div_le_iff₀ (sub_pos.mpr hab)).1 at h
  apply (le_of_mul_le_mul_right ?_ (sub_pos.mpr hab))
  rw [sub_mul, div_mul_cancel₀ _ hn]
  simp only [one_mul, sum_add_distrib, sum_sub_distrib, ← mul_sum] at *
  linarith only [h, show
    (N:ℝ)*(b-a)/4*(b-a) = (N:ℝ)*a^2/2 - 2*((N:ℝ)*((a+b)/2)^2/2) + (N:ℝ)*b^2/2 by ring]

#print axioms star_discrepancy_from_objective
#print axioms chord_bound
#print axioms integrated_discrepancy
#print axioms tent_bound
end
end Kritzinger
