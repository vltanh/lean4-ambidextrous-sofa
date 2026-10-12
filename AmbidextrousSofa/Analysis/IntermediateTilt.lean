module

public import AmbidextrousSofa.Analysis.TiltedDiagonalRoof

@[expose] public section

/-!
# The actual intermediate-width tilt bound

The mandatory affine-ceiling loss is subtracted from the complete
diagonal relaxation. One common price pays the two clipped perspective losses and the niche
apex. The support coordinates cancel, and completing one price square
gives the coupled width/tilt bound without a support optimizer.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

def tiltedDiagonalRelaxation (a h k u v : ℝ) : ℝ :=
  diagonalRelaxation a h k u v - h * (v - a / 2) ^ 2 / (2 * (a - h))

def tiltedDiagonalBound (a h k : ℝ) : ℝ :=
  a - 5 * a * h / 8 - 2 * a * (a - 3 * h / 4 - k) ^ 2 / (4 * a - h)

/-- Completing the ceiling square retains the exact perspective loss. -/
theorem tiltedDiagonalRelaxation_eq_perspective {a h : ℝ}
    (ha : 0 < a) (hha : h < a) (k u v : ℝ) :
    tiltedDiagonalRelaxation a h k u v =
      a - 5 * a * h / 8 -
        ((a - u) ^ 2 + (a - v - h / 2) ^ 2 / (1 - h / a)) / 2 -
        (max ((u + v - h) / 2 - k) 0) ^ 2 +
        ((max (u - k - a / 2) 0) ^ 2 + (max (v - h - k - a / 2) 0) ^ 2) / 2 := by
  unfold tiltedDiagonalRelaxation diagonalRelaxation
  field_simp [ha.ne', (sub_pos.mpr hha).ne']
  ring

/-- One common price pays both clipped exterior losses and the niche apex.
The support coordinates cancel, leaving a single quadratic in that price. -/
theorem tiltedDiagonalRelaxation_le_price {a h k t : ℝ}
    (ha : 0 < a) (hh : 0 ≤ h) (hha : h < a) (ht : 0 ≤ t)
    (hclip : a / 2 - k ≤ t) (ht1 : t / a ≤ 3 / 2) (u v : ℝ) :
    tiltedDiagonalRelaxation a h k u v ≤
      a - 5 * a * h / 8 - 2 * t * (a - 3 * h / 4 - k) +
        (2 - h / a / 2) * t ^ 2 := by
  have hR := clipped_perspective_ge_tangent ha le_rfl ha ht1 (a - u)
    (c := u - k - a / 2) (by linarith only [hclip])
  have hL := clipped_perspective_ge_tangent ha hh hha ht1 (a - v + h)
    (c := v - h - k - a / 2) (by linarith only [hclip])
  have hN := positive_square_ge_tangent ((u + v - h) / 2 - k) ht
  simp only [mul_zero, add_zero, zero_div, sub_zero, div_one] at hR
  rw [show a - v + h - 3 * h / 2 = a - v - h / 2 by ring] at hL
  rw [tiltedDiagonalRelaxation_eq_perspective ha hha]
  linear_combination hR / 2 + hL / 2 + hN

/-- The common price balances the total area loss. The unit-width and
half-height bounds make that price admissible for both clipped tails. -/
theorem tiltedDiagonalRelaxation_le_bound {a h k : ℝ}
    (ha0 : 1 ≤ a) (hh : 0 ≤ h) (hh1 : h < 1 / 2)
    (hk0 : 1 / 3 ≤ k) (hk1 : k ≤ 1 / 2) (u v : ℝ) :
    tiltedDiagonalRelaxation a h k u v ≤ tiltedDiagonalBound a h k := by
  have ha : 0 < a := by linarith only [ha0]
  have hha : h < a := by linarith only [ha0, hh1]
  have h4 : 0 < 4 * a - h := by linarith only [ha, hha]
  have hk : 0 ≤ k := by linarith only [hk0]
  have hclip : h * (a + k) ≤ 2 * a * k := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr ha0)
      (by linarith only [hk0] : 0 ≤ 2 * k - 1 / 2),
      mul_nonneg (by linarith only [hh1] : 0 ≤ 1 / 2 - h) (by linarith only [ha, hk] : 0 ≤ a + k), hk0]
  let t := 2 * a * (a - 3 * h / 4 - k) / (4 * a - h)
  have hprice : t * (4 * a - h) = 2 * a * (a - 3 * h / 4 - k) :=
    div_mul_cancel₀ _ h4.ne'
  have ht : 0 ≤ t := div_nonneg (mul_nonneg (by positivity)
    (by linarith only [ha0, hh1, hk1] : 0 ≤ a - 3 * h / 4 - k)) h4.le
  have htail : a / 2 - k ≤ t := le_of_mul_le_mul_right (by
    nlinarith only [hprice, hclip]) h4
  have hupper : t ≤ a / 2 := le_of_mul_le_mul_right (by
    nlinarith only [hprice, mul_nonneg ha.le (by linarith only [hh, hk] : 0 ≤ h + 2 * k)]) h4
  have hbalance : (2 - h / a / 2) * t = a - 3 * h / 4 - k := by
    field_simp [ha.ne']
    nlinarith only [hprice]
  have hpaid : (2 - h / a / 2) * t ^ 2 = t * (a - 3 * h / 4 - k) := by
    linear_combination t * hbalance
  refine (tiltedDiagonalRelaxation_le_price ha hh hha ht htail
    ((div_le_iff₀ ha).mpr (by linarith only [hupper, ha])) u v).trans_eq ?_
  rw [hpaid]
  dsimp [t]
  unfold tiltedDiagonalBound
  ring

theorem tiltedDiagonalBound_eq_width_tilt {a h k : ℝ} (h4 : 4 * a - h ≠ 0)
    (hksq : k ^ 2 + 2 * k = 1) :
    tiltedDiagonalBound a h k =
      1 - (a - (k + 1)) ^ 2 / 2 - (2 * a / (4 * a - h)) * (k + h / 2) ^ 2 := by
  have h4' : a * 4 - h ≠ 0 := by rwa [mul_comm] at h4
  unfold tiltedDiagonalBound
  field_simp
  linear_combination 128 * (a * 4 - h) * hksq

/-- Compare directly with the generated reference area at height one third. -/
theorem tiltedDiagonalBound_lt_of_large_tilt {a h k : ℝ}
    (ha0 : 1 ≤ a) (ha1 : a ≤ 8 / 5) (hh0 : 1 / 3 ≤ h) (hh1 : h < 1 / 2)
    (hk : diagonalOffsetLower < k) (hksq : k ^ 2 + 2 * k = 1) :
    tiltedDiagonalBound a h k < referenceHalfAreaLower := by
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  have h4 : 0 < 4 * a - h := by linarith only [ha0, hh1]
  have hcoef : (2 * (8 / 5) / (4 * (8 / 5) - 1 / 3) : ℝ) ≤ 2 * a / (4 * a - h) := by
    rw [le_div_iff₀ h4]
    norm_num
    linarith only [ha1, hh0]
  have hq : (diagonalOffsetLower + 1 / 6 : ℝ) < k + h / 2 := by
    linarith only [hk, hh0]
  have hendpoint : 1 - (2 * (8 / 5) / (4 * (8 / 5) - 1 / 3)) *
      (diagonalOffsetLower + 1 / 6) ^ 2 < referenceHalfAreaLower := by
    norm_num [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton, referenceHalfAreaLower,
      referenceRootLower, cubicBracketLower, cubicBracketUpper, cubic]
  rw [tiltedDiagonalBound_eq_width_tilt h4.ne' hksq]
  nlinarith only [hendpoint, mul_pos (sub_pos.mpr hq) (by linarith only [hk, hh0] :
    0 < k + h / 2 + (diagonalOffsetLower + 1 / 6 : ℝ)), mul_nonneg (sub_nonneg.mpr hcoef)
    (sq_nonneg (k + h / 2)), sq_nonneg (a - (k + 1))]

/-- A high score leaves the coupled width and tilt within the reference area budget. -/
theorem tiltedDiagonalBound_high_score {a h k : ℝ}
    (ha0 : 1 ≤ a) (ha1 : a ≤ 8 / 5) (hh1 : h < 1 / 2)
    (hk : diagonalOffsetLower < k) (hksq : k ^ 2 + 2 * k = 1)
    (hscore : referenceHalfAreaLower ≤ tiltedDiagonalBound a h k) :
    h < 1 / 3 ∧ (a - (k + 1)) ^ 2 +
      (4 * a / (4 * a - h)) * (k + h / 2) ^ 2 ≤ 2 * (1 - referenceHalfAreaLower) := by
  refine ⟨lt_of_not_ge fun h' => not_lt_of_ge hscore
    (tiltedDiagonalBound_lt_of_large_tilt ha0 ha1 h' hh1 hk hksq), ?_⟩
  rw [tiltedDiagonalBound_eq_width_tilt (by linarith only [ha0, hh1]) hksq] at hscore
  rw [show 4 * a / (4 * a - h) = 2 * (2 * a / (4 * a - h)) by ring]
  linarith only [hscore]

/-- INT.1 for the actual tilted cap, including every diagonal clipping
configuration. Only the original cap's middle geometry is assumed. -/
theorem IsDownwardCap.capScore_le_tiltedDiagonalBound
    {U : Set Plane} (hU : IsDownwardCap U) {a h α : ℝ}
    (ha : 1 ≤ a) (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hα0 : Real.pi / 4 ≤ α) (hαL : α ≤ Real.pi / 2) :
    capScore U α ≤ tiltedDiagonalBound a h (Real.sqrt 2 - 1) := by
  have ha0 : 0 < a := by linarith only [ha]
  have hhhalf : h ≤ a / 2 := by linarith only [ha, hh1]
  have huv := hU.tilted_diagonal_parameters_mem ha0 hh0 hhhalf hl hr hleft hright
  have hD := hU.diagonalRoofDeficit_ge_tilt_loss ha0 (by linarith only [ha, hh1]) hl hr hleft
    hright haffine (by ring) (by ring) huv.1 huv.2
  have hk := sqrt_two_sub_one_bounds
  have hscalar := tiltedDiagonalRelaxation_le_bound (k := Real.sqrt 2 - 1) ha hh0 hh1
    (by norm_num [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at hk; linarith)
    (by norm_num [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at hk; linarith)
    (diagonalRight U - 1) (diagonalLeft U - 1 + h)
  unfold tiltedDiagonalRelaxation at hscalar
  linarith only [hD, hscalar,
    hU.capScore_add_diagonalRoofDeficit_le ha0 hh0 hhhalf hl hr hleft hright hα0 hαL]

theorem IsDownwardCap.intermediate_width_tilt_bound
    {U : Set Plane} (hU : IsDownwardCap U) {a h α : ℝ}
    (ha0 : 1 ≤ a) (ha1 : a ≤ 8 / 5) (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hα0 : Real.pi / 4 ≤ α) (hαL : α ≤ Real.pi / 2)
    (hscore : referenceHalfAreaLower ≤ capScore U α) :
    h < 1 / 3 ∧ (a - Real.sqrt 2) ^ 2 +
      (4 * a / (4 * a - h)) * (Real.sqrt 2 - 1 + h / 2) ^ 2 ≤ 2 * (1 - referenceHalfAreaLower) := by
  have hP := hU.capScore_le_tiltedDiagonalBound ha0 hh0 hh1 hl hr hleft hright haffine hα0 hαL
  simpa only [show Real.sqrt 2 - 1 + 1 = Real.sqrt 2 by ring] using
    tiltedDiagonalBound_high_score ha0 ha1 hh1 sqrt_two_sub_one_bounds.1
      sqrt_two_sub_one_quadratic (hscore.trans hP)

end AmbidextrousSofa
