module

public import AmbidextrousSofa.Analysis.WideDiagonalGeometry

@[expose] public section

/-!
# Diagonal geometry of the literal three-angle objective

The unchanged actual roof deficits subtract from this finite objective.
Its diagonal member alone supplies the wide peak-fitting bound and the
intermediate tilt bound. These are comparisons for every cap in the
stated geometric form, so they also apply to the cap used only for
comparative reflection.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

/-- The endpoint height sum and a high three-angle score directly place both nearby-angle peaks in the middle window. -/
theorem IsDownwardCap.threeAngle_wide_high_score_fitting {U : Set Plane}
    (hU : IsDownwardCap U) {a h : ℝ} (ha0 : 8 / 5 ≤ a) (ha1 : a < 3)
    (hh : 0 ≤ h) (hh1 : h < 1 / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hEP : 1 - h / 2 ≤ capRoof U a + capRoof U (-a))
    (hscore : 41 / 50 ≤ intervalSpatialScore (capRoof U) (threeAngleBarrier U)
      (horizontalLeft U) (horizontalRight U)) :
    a ≤ 1 + 2 * (Real.sqrt 2 - 1) ∧
      (1 - (Real.sqrt 2 - 1) / 2) * a + h <
        (1 + (Real.sqrt 2 - 1)) * nearDiagonalNorm (Real.sqrt 2 - 1) := by
  have ha : 0 < a := by linarith only [ha0]
  have hhhalf : h ≤ a / 2 := by linarith only [ha0, hh1]
  have hk := sqrt_two_sub_one_bounds
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  have hm := hU.wide_diagonal_midpoint_ge ha hh hhhalf hl hr hleft hright haffine hEP
  have hp := hU.wide_diagonal_parameters ha hh hhhalf hl hr hleft hright haffine
  have hD := hU.wideRoofDeficit_eq ha (by linarith only [ha, hhhalf]) hp.1 hp.2.1
  have hN := hU.diagonal_tent_le_integral (continuous_threeAngleBarrier U).intervalIntegrable
    (fun x => le_max_left _ _) (a := a) (h := 0) (u := diagonalRight U - 1)
    (v := diagonalLeft U - 1) rfl (by ring) (by ring)
    ⟨by linarith only [hp.1.1, hp.2.1.2, hh, ha], by linarith only [hp.1.2, hp.2.1.1, hhhalf]⟩
  have hm' : Real.sqrt 2 - 1 ≤ (diagonalRight U - 1 + (diagonalLeft U - 1)) / 2 := by
    linarith only [hm, ha0, hh1, hk.2.2]
  simp only [sub_zero, max_eq_left (sub_nonneg.mpr hm')] at hN
  rw [hl, hr, intervalSpatialScore_centered] at hscore
  refine wide_diagonal_high_score_fitting ha0 ha1 hh hh1 hk.1 hk.2.2 sqrt_two_sub_one_quadratic hm ?_
  rw [wideDiagonalMajorant]
  rw [wideExteriorMajorant] at hD
  linarith only [hscore, hD, hN, hU.wideRoofDeficit_nonneg ha hl hr hleft hright haffine]

theorem IsDownwardCap.threeAngle_intermediate_width_tilt_bound {U : Set Plane}
    (hU : IsDownwardCap U) {a h : ℝ}
    (ha0 : 1 ≤ a) (ha1 : a ≤ 8 / 5) (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hscore : referenceHalfAreaLower ≤ intervalSpatialScore (capRoof U) (threeAngleBarrier U)
      (horizontalLeft U) (horizontalRight U)) :
    h < 1 / 3 ∧ (a - Real.sqrt 2) ^ 2 +
      (4 * a / (4 * a - h)) * (Real.sqrt 2 - 1 + h / 2) ^ 2 ≤ 2 * (1 - referenceHalfAreaLower) := by
  have ha : 0 < a := by linarith only [ha0]
  have hhhalf : h ≤ a / 2 := by linarith only [ha0, hh1]
  have hk := sqrt_two_sub_one_bounds
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  have hksq := sqrt_two_sub_one_quadratic
  have huv := hU.tilted_diagonal_parameters_mem ha hh0 hhhalf hl hr hleft hright
  have hD := hU.diagonalRoofDeficit_ge_tilt_loss ha (by linarith only [ha0, hh1]) hl hr hleft
    hright haffine (by ring) (by ring) huv.1 huv.2
  have hP := hU.score_add_diagonalRoofDeficit_le (continuous_threeAngleBarrier U).intervalIntegrable
    (fun x => le_max_left _ _) ha hh0 hhhalf hl hr hleft hright
  have hscalar := tiltedDiagonalRelaxation_le_bound (k := Real.sqrt 2 - 1) ha0 hh0 hh1
    (by linarith only [hk.1]) (by linarith only [hk.2.1])
    (diagonalRight U - 1) (diagonalLeft U - 1 + h)
  rw [tiltedDiagonalRelaxation] at hscalar
  rw [hl, hr] at hscore
  have hB : intervalSpatialScore (capRoof U) (threeAngleBarrier U) (-a) a ≤
      tiltedDiagonalBound a h (Real.sqrt 2 - 1) := by
    linarith only [hD, hP, hscalar]
  simpa only [show Real.sqrt 2 - 1 + 1 = Real.sqrt 2 by ring] using
    tiltedDiagonalBound_high_score ha0 ha1 hh1 hk.1 hksq (hscore.trans hB)

end AmbidextrousSofa
