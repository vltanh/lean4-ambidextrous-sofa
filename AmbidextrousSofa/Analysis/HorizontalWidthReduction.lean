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
constraint then contradicts that row. Consequently the geometric
orientation and unit-curvature theorem applies without a supplied width
or source certificate.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

/-- The width and both unit-density bounds are derived from the actual
horizontal maximum. The choice of orientation remains explicit. -/
theorem IsFullCapMaximizer.exists_horizontal_oriented_unit_density
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = 1) :
    ∃ V : Set Plane, (V = U ∨ V = AmbidextrousSofa.horizontalMirror U) ∧ IsFullCapMaximizer V ∧
      horizontalLeft V = -2 * C ∧ horizontalRight V = 2 * C ∧
      capHeight V = 1 ∧ capWidth V = capWidth U ∧
      capScore V (Real.pi / 2) = capScore U (Real.pi / 2) ∧
      (∀ x ∈ middleHalfInterval (horizontalLeft V) (horizontalRight V), capRoof V x = 1) ∧
      ∃ ρ : ℝ → ℝ, Measurable ρ ∧
        (∀ t, 0 ≤ ρ t ∧ ρ t ≤ 1 ∧ ρ t ≤ sourceKappa (upperCornerVelocity V t)) ∧
        (upperCurvature V).restrict (regularCurvatureDomain 0) =
          (volume.restrict (regularCurvatureDomain 0)).withDensity (fun t => ENNReal.ofReal (ρ t)) := by
  have hw := hU.isCap.capWidth_nonneg
  have hC1 := hU.quarter_width_lt_thirty_seven_fiftieths
  rw [capWidth, hl, hr] at hw hC1
  refine hU.exists_horizontal_oriented_unit_density_of_width_le hl hr (by linarith) ?_
    hheight hmiddle
  by_contra! hC0
  obtain ⟨R, haC, hCb⟩ := exists_horizontalLeakageRow hC0.le (by linarith)
  obtain ⟨hnL, hnR⟩ :=
    hU.endpoint_niches_le_horizontalLeakageRow R hl hr hheight hmiddle (by linarith) haC hCb
  exact hU.false_of_horizontal_leakage_row R hl hr (by linarith) haC hheight hmiddle hnL hnR

end AmbidextrousSofa
