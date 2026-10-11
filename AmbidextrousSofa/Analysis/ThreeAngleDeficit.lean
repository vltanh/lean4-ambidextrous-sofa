module

public import AmbidextrousSofa.Analysis.WideDiagonalGeometry

@[expose] public section

/-!
# Diagonal geometry of the literal three-angle objective

The unchanged actual roof deficits subtract from this finite objective.
Its diagonal member alone supplies the wide high-score box and the
intermediate tilt bound. These are comparisons for every cap in the
stated geometric form, so they also apply to the cap used only for
comparative reflection.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

/-- The endpoint height sum and a high three-angle score force the compact small-tilt box. -/
theorem IsDownwardCap.threeAngle_wide_high_score_box {U : Set Plane}
    (hU : IsDownwardCap U) {a h : ℝ} (ha0 : 8 / 5 ≤ a) (ha1 : a < 3)
    (hh : 0 ≤ h) (hh1 : h < 1 / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hEP : 1 - h / 2 ≤ capRoof U a + capRoof U (-a))
    (hscore : 41 / 50 ≤ intervalSpatialScore (capRoof U) (threeAngleBarrier U)
      (horizontalLeft U) (horizontalRight U)) :
    a < 9 / 5 ∧ h < 1 / 4 ∧ a + h < 37 / 20 := by
  have ha : 0 < a := by linarith only [ha0]
  have hhhalf : h ≤ a / 2 := by linarith only [ha0, hh1]
  have hk := sqrt_two_sub_one_strict_bounds
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
  refine wide_diagonal_high_score_box ha0 ha1 hh hh1 hk.1 hk.2.2 sqrt_two_sub_one_quadratic hm ?_
  rw [wideDiagonalMajorant]
  rw [wideExteriorMajorant] at hD
  linarith only [hscore, hD, hN, hU.wideRoofDeficit_nonneg ha hl hr hleft hright haffine]

theorem IsDownwardCap.threeAngle_intermediate_width_tilt_bound {U : Set Plane}
    (hU : IsDownwardCap U) {a h : ℝ}
    (ha0 : 1 ≤ a) (ha1 : a ≤ 8 / 5) (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hscore : 41 / 50 ≤ intervalSpatialScore (capRoof U) (threeAngleBarrier U)
      (horizontalLeft U) (horizontalRight U)) :
    h < 17 / 50 ∧ (a - Real.sqrt 2) ^ 2 +
      (4 * a / (4 * a - h)) * (Real.sqrt 2 - 1 + h / 2) ^ 2 ≤ 9 / 25 := by
  have ha : 0 < a := by linarith only [ha0]
  have hhhalf : h ≤ a / 2 := by linarith only [ha0, hh1]
  have hk := sqrt_two_sub_one_strict_bounds
  have hksq := sqrt_two_sub_one_quadratic
  have huv := hU.tilted_diagonal_parameters_mem ha hh0 hhhalf hl hr hleft hright
  have hD := hU.diagonalRoofDeficit_ge_tilt_loss ha (by linarith only [ha0, hh1]) hl hr hleft
    hright haffine (by ring) (by ring) huv.1 huv.2
  have hP := hU.score_add_diagonalRoofDeficit_le (continuous_threeAngleBarrier U).intervalIntegrable
    (fun x => le_max_left _ _) ha hh0 hhhalf hl hr hleft hright
  have hscalar := tiltedDiagonalRelaxation_le_bound ha0 hh0 hh1 hk.1 hk.2.1
    (diagonalRight U - 1) (diagonalLeft U - 1 + h)
  rw [tiltedDiagonalRelaxation] at hscalar
  rw [hl, hr] at hscore
  have hB : intervalSpatialScore (capRoof U) (threeAngleBarrier U) (-a) a ≤
      tiltedDiagonalBound a h (Real.sqrt 2 - 1) := by
    linarith only [hD, hP, hscalar]
  refine ⟨lt_of_not_ge fun h' => not_lt_of_ge hscore (hB.trans_lt
    (tiltedDiagonalBound_lt_of_large_tilt ha0 ha1 h' hh1 (by linarith only [hk.1]) hksq)), ?_⟩
  rw [tiltedDiagonalBound_eq_width_tilt (by linarith only [ha0, hh1]) hksq,
    show Real.sqrt 2 - 1 + 1 = Real.sqrt 2 by ring] at hB
  rw [show 4 * a / (4 * a - h) = 2 * (2 * a / (4 * a - h)) by ring]
  linarith only [hB, hscore]

end AmbidextrousSofa
