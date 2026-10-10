import AmbidextrousSofa.Analysis.HorizontalLeakageBound
import AmbidextrousSofa.Analysis.HorizontalOrdinaryArea
import AmbidextrousSofa.Analysis.HorizontalUnitCurvature

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

theorem IsFullCapMaximizer.horizontal_quarter_width_lt_energy_threshold
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = 1) : C < 8571 / 12500 := by
  by_contra hnot
  have hC0 : 8571 / 12500 ≤ C := le_of_not_gt hnot
  have hquarter : capWidth U / 4 = C := by
    unfold capWidth
    rw [hl, hr]
    ring
  have hC1 := hU.quarter_width_lt_thirty_seven_fiftieths
  rw [hquarter] at hC1
  obtain ⟨R, haC, hCb⟩ := exists_horizontalLeakageRow hC0
    (show C ≤ 4 / 5 by linarith only [hC1])
  obtain ⟨hnL, hnR⟩ := hU.endpoint_niches_le_horizontalLeakageRow R hl hr
    hheight hmiddle (show 2 / 3 < C by linarith only [hC0]) haC hCb
  exact hU.false_of_horizontal_leakage_row R hl hr
    (show 1 / 2 ≤ C by linarith only [hC0]) haC hheight hmiddle hnL hnR

/-- The width and both unit-density bounds are derived from the actual
horizontal maximum. The choice of orientation remains explicit. -/
theorem IsFullCapMaximizer.exists_horizontal_oriented_unit_density
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = 1) :
    ∃ V : Set Plane, (V = U ∨ V = horizontalMirror U) ∧ IsFullCapMaximizer V ∧
      horizontalLeft V = -2 * C ∧ horizontalRight V = 2 * C ∧
      capHeight V = 1 ∧ capWidth V = capWidth U ∧
      capScore V (Real.pi / 2) = capScore U (Real.pi / 2) ∧
      (∀ x ∈ middleHalfInterval (horizontalLeft V) (horizontalRight V), capRoof V x = 1) ∧
      ∃ ρ : ℝ → ℝ, Measurable ρ ∧
        (∀ t, 0 ≤ ρ t ∧ ρ t ≤ 1 ∧ ρ t ≤ sourceKappa (upperCornerVelocity V t)) ∧
        (upperCurvature V).restrict (regularCurvatureDomain 0) =
          (volume.restrict (regularCurvatureDomain 0)).withDensity (fun t => ENNReal.ofReal (ρ t)) := by
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  rw [hl, hr] at hlr
  exact hU.exists_horizontal_oriented_unit_density_of_width_le hl hr
    (by linarith only [hlr])
    (hU.horizontal_quarter_width_lt_energy_threshold hl hr hheight hmiddle).le hheight hmiddle

end AmbidextrousSofa
