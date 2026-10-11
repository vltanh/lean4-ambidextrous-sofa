module

public import AmbidextrousSofa.Analysis.HorizontalLeakageBound
public import AmbidextrousSofa.Analysis.HorizontalOrdinaryArea
public import AmbidextrousSofa.Analysis.HorizontalUnitCurvature

@[expose] public section

/-!
# The actual horizontal leakage width reduction

Every actual horizontal full maximum wider than the energy threshold
lies in one of the explicit rational rows. Its own selected curvature
density gives both endpoint leakage estimates. The actual one-turn area
constraint then contradicts that row. This bound is the width hypothesis
of the geometric orientation and unit-curvature theorem, which therefore
applies without a supplied width or source certificate.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

/-- The quarter width of an actual horizontal maximum is at most the energy threshold. -/
theorem IsFullCapMaximizer.horizontal_quarter_width_le
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = 1) : C ≤ 8571 / 12500 := by
  have hC1 := hU.quarter_width_lt_thirty_seven_fiftieths
  rw [capWidth, hl, hr] at hC1
  by_contra! hC0
  obtain ⟨R, haC, hCb⟩ := exists_horizontalLeakageRow hC0.le (by linarith)
  obtain ⟨hnL, hnR⟩ :=
    hU.endpoint_niches_le_horizontalLeakageRow R hl hr hheight hmiddle (by linarith) haC hCb
  exact hU.false_of_horizontal_leakage_row R hl hr (by linarith) haC hheight hmiddle hnL hnR

end AmbidextrousSofa
