module

public import AmbidextrousSofa.Analysis.TiltedInitialCircle
public import AmbidextrousSofa.Analysis.TiltedEndpointBounds

@[expose] public section

/-!
# Actual parameter regions for first-wing unit curvature

Endpoint pressure and the literal middle niche bounds supply the scalar
initial-floor conditions in the high-tilt and dry-left middle-tilt
regions.
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

theorem IsFullCapMaximizer.initial_floor_conditions_of_high_tilt
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 2 / 3 ≤ C) (hC1 : C ≤ 37 / 50)
    (hh0 : 21 / 100 ≤ h) (hh1 : h ≤ 17 / 50)
    (hm : 0 ≤ m) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1) :
    Analysis.InitialFloorEnergyConditions (3 * C)
      (capRoof U (horizontalRight U) - 1 + h) h := by
  rw [hU.tilted_endpoint_momentum_eq hl hr hheight haffine hlow hhigh]
  have hn := hU.isCap.middle_niche_le_box_height_of_endpoints hl hr
    (by linarith only [hC0]) (by linarith only [hC1])
  have hw := hU.isCap.left_middle_niche_le_tilted_box hl hr
    (by linarith only [hC0]) (by linarith only [hC1]) hm haffine hlow
  exact Analysis.initialFloorEnergyConditions_high_tilt hC0 hC1 hh0 hh1
    (sweptNiche_nonneg U (Real.pi / 2) C) hn.2
    (sweptNiche_nonneg U (Real.pi / 2) (-C)) hw

theorem IsFullCapMaximizer.initial_floor_conditions_of_middle_tilt_low_width
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 2 / 3 ≤ C) (hC1 : C ≤ 73 / 100)
    (hh0 : 1 / 20 ≤ h) (hh1 : h ≤ 21 / 100) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1)
    (hdry : sweptNiche U (Real.pi / 2) (-C) = 0) :
    Analysis.InitialFloorEnergyConditions (3 * C)
      (capRoof U (horizontalRight U) - 1 + h) h := by
  rw [hU.tilted_endpoint_momentum_eq hl hr hheight haffine hlow hhigh, hdry]
  have hn := hU.isCap.middle_niche_le_box_height_of_endpoints hl hr
    (by linarith only [hC0]) (by linarith only [hC1])
  exact Analysis.initialFloorEnergyConditions_middle_tilt_low_width
    hC0 hC1 hh0 hh1 (sweptNiche_nonneg U (Real.pi / 2) C) hn.2

end AmbidextrousSofa
