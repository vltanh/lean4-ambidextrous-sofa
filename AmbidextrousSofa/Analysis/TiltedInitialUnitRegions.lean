module

public import AmbidextrousSofa.Analysis.TiltedInitialCircle
public import AmbidextrousSofa.Analysis.TiltedEndpointBounds

@[expose] public section

/-!
# Actual parameter regions for first-wing unit curvature

Endpoint pressure and the dry low endpoint supply the scalar
initial-floor conditions below the width determined by the initial radius.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem IsFullCapMaximizer.tilted_endpoint_momentum_eq
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1) :
    capRoof U (horizontalRight U) - 1 + h =
      Analysis.tiltedEndpointMomentum h (sweptNiche U (Real.pi / 2) C)
        (sweptNiche U (Real.pi / 2) (-C)) := by
  unfold Analysis.tiltedEndpointMomentum
  linarith only [(hU.tilted_endpoint_laws hl hr hheight haffine hlow hhigh).1]

/-- The dry low endpoint supplies the momentum bounds for the single
radius-defined comparison width. -/
theorem IsFullCapMaximizer.initial_floor_conditions_of_radius_width
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 2 / 3 ≤ C) (hC1 : C ≤ Analysis.tiltedRadiusWidth)
    (hh0 : Analysis.tiltedBalanceHeight ≤ h) (hh1 : h ≤ 1 / 3) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1)
    (hdry : sweptNiche U (Real.pi / 2) (-C) = 0) :
    Analysis.InitialFloorEnergyConditions (3 * C)
      (capRoof U (horizontalRight U) - 1 + h) h := by
  rw [hU.tilted_endpoint_momentum_eq hl hr hheight haffine hlow hhigh, hdry]
  have hwidth : C ≤ 37 / 50 := hC1.trans
    (Analysis.tiltedRadiusWidth_bounds.2.trans Analysis.tiltedRadius_comparison_brackets.2.2).le
  have hn := hU.isCap.middle_niche_le_box_height_of_endpoints hl hr
    (by linarith only [hC0]) (by linarith only [hwidth])
  exact Analysis.initialFloorEnergyConditions_of_radius_width
    hC0 hC1 hh0 hh1 (sweptNiche_nonneg U (Real.pi / 2) C) hn.2

end AmbidextrousSofa
