module

public import AmbidextrousSofa.Analysis.DiagonalRelaxation

@[expose] public section

/-!
# Exact global bounds for the clipped diagonal relaxation

The positive square has a global supporting tangent. Each clipped tail
square is at most the squared displacement from an inactive tail at the
comparison point. These three elementary inequalities give a global
supporting plane for the full relaxation at every positive, unclipped
comparison point. The critical and constrained-critical comparisons
therefore require no differentiability across a clipping boundary.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem positive_square_ge_tangent (x : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    y ^ 2 + 2 * y * (x - y) ≤ (max x 0) ^ 2 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx]
    nlinarith [sq_nonneg (x - y)]
  · rw [max_eq_right (le_of_not_ge hx)]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hy (le_of_not_ge hx), sq_nonneg y]

theorem shifted_positive_square_le_displacement (x : ℝ) {c z : ℝ} (hz : z ≤ c) :
    (max (x - c) 0) ^ 2 ≤ (x - z) ^ 2 := by
  by_cases hx : x ≤ c
  · rw [max_eq_right (sub_nonpos.mpr hx)]
    simpa using sq_nonneg (x - z)
  · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge hx))]
    nlinarith [mul_nonneg (sub_nonneg.mpr hz)
      (show 0 ≤ 2 * x - c - z by linarith)]

theorem diagonalRelaxation_le_tangent (a h k u v u0 v0 : ℝ)
    (hq : 0 ≤ (u0 + v0 - h) / 2 - k)
    (hu0 : u0 ≤ k + a / 2) (hv0 : v0 ≤ h + k + a / 2) :
    diagonalRelaxation a h k u v ≤
      a - ((a - u0) ^ 2 + (a - v0) ^ 2) / 2 - a * h / 2 -
        ((u0 + v0 - h) / 2 - k) ^ 2 +
      (a - u0 - ((u0 + v0 - h) / 2 - k)) * (u - u0) +
      (a - v0 - ((u0 + v0 - h) / 2 - k)) * (v - v0) := by
  have hcore := positive_square_ge_tangent ((u + v - h) / 2 - k) hq
  have hright := shifted_positive_square_le_displacement u hu0
  have hleft := shifted_positive_square_le_displacement v hv0
  rw [show u - (k + a / 2) = u - k - a / 2 by ring] at hright
  rw [show v - (h + k + a / 2) = v - h - k - a / 2 by ring] at hleft
  unfold diagonalRelaxation
  nlinarith

theorem diagonalRelaxation_le_critical (a h k u v : ℝ)
    (hq : k + h / 2 ≤ a) (hleft : -2 * k / 3 ≤ h) (hright : h ≤ 2 * k) :
    diagonalRelaxation a h k u v ≤ a - (a - k) ^ 2 / 2 - k * h / 2 - h ^ 2 / 8 := by
  have h := diagonalRelaxation_le_tangent a h k u v
    ((a + k + h / 2) / 2) ((a + k + h / 2) / 2)
    (by linarith) (by linarith) (by linarith)
  convert h using 1 <;> ring

theorem diagonal_critical_width_mono {a A k : ℝ} (ha : a ≤ A)
    (hA : A ≤ 1 + k) : a - (a - k) ^ 2 / 2 ≤ A - (A - k) ^ 2 / 2 := by
  have h := mul_nonneg (sub_nonneg.mpr ha)
    (show 0 ≤ 1 + k - (A + a) / 2 by linarith)
  nlinarith

theorem diagonalRelaxation_le_constrained_right (a h k t u v : ℝ)
    (hq : 0 ≤ a / 2 + t / 3 - 2 * k / 3 - h / 4)
    (ht : k / 2 ≤ t) (hh0 : 0 ≤ h) (hclip : t + h / 4 ≤ k)
    (hu : a / 2 + t + h / 4 ≤ u) :
    diagonalRelaxation a h k u v ≤
      a - (a - k) ^ 2 / 2 - k * h / 2 - h ^ 2 / 8 -
        (2 / 3) * (t - k / 2) ^ 2 := by
  have hsmall : (2 * k - t) / 3 ≤ t := by linarith
  have htan := diagonalRelaxation_le_tangent a h k u v
    (a / 2 + t + h / 4) (a / 2 + (2 * k - t) / 3 + h / 4)
    (by linarith) (by linarith) (by linarith)
  have hgrad : (2 * k - 4 * t) / 3 * (u - (a / 2 + t + h / 4)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.mpr hu)
  nlinarith

theorem diagonalRelaxation_le_constrained_left (a h k t u v : ℝ)
    (hq : 0 ≤ a / 2 + t / 3 - 2 * k / 3 - h / 4)
    (ht : k / 2 ≤ t) (hh0 : 0 ≤ h) (hclip : t + h / 4 ≤ k)
    (hv : a / 2 + t + h / 4 ≤ v) :
    diagonalRelaxation a h k u v ≤
      a - (a - k) ^ 2 / 2 - k * h / 2 - h ^ 2 / 8 -
        (2 / 3) * (t - k / 2) ^ 2 := by
  have hsmall : (2 * k - t) / 3 ≤ t := by linarith
  have htan := diagonalRelaxation_le_tangent a h k u v
    (a / 2 + (2 * k - t) / 3 + h / 4) (a / 2 + t + h / 4)
    (by linarith) (by linarith) (by linarith)
  have hgrad : (2 * k - 4 * t) / 3 * (v - (a / 2 + t + h / 4)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.mpr hv)
  nlinarith

theorem sqrt_two_sub_one_quadratic :
    (Real.sqrt 2 - 1) ^ 2 + 2 * (Real.sqrt 2 - 1) = (1 : ℝ) := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem sqrt_two_sub_one_strict_bounds :
    (2 / 5 : ℝ) < Real.sqrt 2 - 1 ∧ Real.sqrt 2 - 1 < 169 / 408 ∧
      Real.sqrt 2 - 1 < 29 / 70 := by
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hroot := Real.sqrt_nonneg (2 : ℝ)
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- The high-score short-width region is forced into a small, unclipped
neighborhood. All constants are rational apart from the exact diagonal
offset relation. The conclusion is used by the actual extra-tail proof. -/
theorem short_diagonal_stability {a h k u v : ℝ}
    (ha0 : 41 / 50 ≤ a) (ha1 : a ≤ 1001 / 1000)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 37 / 100)
    (hk0 : 2 / 5 < k) (hk1 : k < 169 / 408) (hk2 : k < 29 / 70)
    (hksq : k ^ 2 + 2 * k = 1)
    (hu : u ∈ Icc (a / 2) a) (hv : v ∈ Icc (a / 2) a)
    (hscore : 41 / 50 ≤ diagonalRelaxation a h k u v) :
    9 / 10 < a ∧ h < 1 / 23 ∧
      u - a / 2 < 323 / 1000 + h / 4 ∧
      v - a / 2 < 323 / 1000 + h / 4 ∧
      16 / 25 < (u + v) / 2 - h / 4 ∧
      0 < (u + v - h) / 2 - k ∧
      u - k - a / 2 < 0 ∧ v - h - k - a / 2 < 0 := by
  have hcritical := diagonalRelaxation_le_critical a h k u v
    (by linarith) (by linarith) (by linarith)
  have hwidth := diagonal_critical_width_mono ha1
    (by linarith : (1001 / 1000 : ℝ) ≤ 1 + k)
  have hkh : 0 ≤ k * h := mul_nonneg (by linarith) hh0
  have hmax : diagonalRelaxation a h k u v ≤
      (2001 / 1000) * k - 1 / 2000000 - k * h / 2 - h ^ 2 / 8 := by
    linarith
  have ha : 9 / 10 < a := by
    by_contra hbad
    have hsmall := diagonal_critical_width_mono (le_of_not_gt hbad)
      (by linarith : (9 / 10 : ℝ) ≤ 1 + k)
    linarith [sq_nonneg h]
  have hh : h < 1 / 23 := by
    by_contra hbad
    have hh' : 1 / 23 ≤ h := le_of_not_gt hbad
    have hprod := mul_nonneg (show 0 ≤ k by linarith) (sub_nonneg.mpr hh')
    have hsquare : (1 / 23 : ℝ) ^ 2 ≤ h ^ 2 := by nlinarith [sq_nonneg (h - 1 / 23)]
    linarith
  have hright : u - a / 2 < 323 / 1000 + h / 4 := by
    by_contra hbad
    have hconstrained := diagonalRelaxation_le_constrained_right a h k (323 / 1000) u v
      (by linarith) (by linarith) hh0 (by linarith) (by linarith [le_of_not_gt hbad])
    linarith [sq_nonneg h]
  have hleft : v - a / 2 < 323 / 1000 + h / 4 := by
    by_contra hbad
    have hconstrained := diagonalRelaxation_le_constrained_left a h k (323 / 1000) u v
      (by linarith) (by linarith) hh0 (by linarith) (by linarith [le_of_not_gt hbad])
    linarith [sq_nonneg h]
  have hq : 0 < (u + v - h) / 2 - k := by linarith [hu.1, hv.1]
  have hclipR : u - k - a / 2 < 0 := by linarith
  have hclipL : v - h - k - a / 2 < 0 := by linarith
  have heq : diagonalRelaxation a h k u v =
      a - (a - ((u + v) / 2 - h / 4)) ^ 2 - (((u + v) / 2 - h / 4) - k) ^ 2 -
        ((u - v) / 2) ^ 2 - k * h / 2 - h ^ 2 / 8 := by
    unfold diagonalRelaxation
    rw [max_eq_left hq.le, max_eq_right hclipR.le, max_eq_right hclipL.le]
    ring
  have hm : 16 / 25 < (u + v) / 2 - h / 4 := by
    by_contra hbad
    let m := (u + v) / 2 - h / 4
    have hm0 : m ≤ 16 / 25 := le_of_not_gt hbad
    have hgradA := mul_nonneg (by norm_num : (0 : ℝ) ≤ 139 / 500)
      (sub_nonneg.mpr ha1)
    have hgradM := mul_nonneg (show 0 ≤ 2 * (k - 279 / 1000) by linarith)
      (sub_nonneg.mpr hm0)
    have hquad1 := sq_nonneg ((a - 1001 / 1000) - (m - 16 / 25))
    have hquad2 := sq_nonneg (m - 16 / 25)
    have hbound : a - (a - m) ^ 2 - (m - k) ^ 2 ≤
        (82 / 25) * k - 538921 / 1000000 := by linarith
    change diagonalRelaxation a h k u v =
      a - (a - m) ^ 2 - (m - k) ^ 2 - ((u - v) / 2) ^ 2 - k * h / 2 - h ^ 2 / 8 at heq
    linarith [sq_nonneg ((u - v) / 2), sq_nonneg h]
  exact ⟨ha, hh, hright, hleft, hm, hq, hclipR, hclipL⟩

end AmbidextrousSofa
