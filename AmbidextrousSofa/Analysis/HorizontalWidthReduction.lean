module

public import AmbidextrousSofa.Analysis.SmallTiltConstants
public import AmbidextrousSofa.Analysis.HorizontalOrdinaryArea
public import AmbidextrousSofa.Analysis.HorizontalUnitCurvature

@[expose] public section

/-!
# Horizontal width reduction by a chord and the 3–4–5 direction

Above `2/3`, the niche vanishes at both middle endpoints, so the ordinary
survivor has area at least `2C + sqrt (C² + 1/4)`. Its supporting line in
the unit direction `(4/5, 3/5)` already exceeds the ordinary-sofa bound at
`C = sqrt 17 / 6`. Below that width, the endpoint energy controls curvature.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

/-- A horizontal maximum has quarter width strictly below the energy threshold. -/
theorem IsFullCapMaximizer.horizontal_quarter_width_lt_energy
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = 1) : C < horizontalEnergyWidth := by
  by_contra! hC
  have hlarge : 2 / 3 < C := horizontalEnergyWidth_gt_two_thirds.trans_le hC
  have harea := hU.horizontal_ordinary_area_bound hl hr hheight hmiddle hlarge
  have htangent := Analysis.smallTilt_tangent_le_norm C (1 / 2)
  norm_num at htangent
  have hbaseline := Analysis.smallTilt_baseline_gt_ordinary_bound
  have hcompare : Analysis.smallTiltBaseline ≤
      (2 + Analysis.smallTiltTangent) * C + Analysis.smallTiltVertical / 2 := by
    change (2 + 4 / 5 : ℝ) * horizontalEnergyWidth + (3 / 5) / 2 ≤
      (2 + 4 / 5 : ℝ) * C + (3 / 5) / 2
    linarith only [hC]
  unfold Analysis.smallTiltTangent Analysis.smallTiltVertical at htangent hcompare
  linarith

/-- The energy test therefore applies to every horizontal maximum. -/
theorem IsFullCapMaximizer.horizontal_quarter_width_le
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = 1) : C ≤ horizontalEnergyWidth :=
  (hU.horizontal_quarter_width_lt_energy hl hr hheight hmiddle).le

end AmbidextrousSofa
