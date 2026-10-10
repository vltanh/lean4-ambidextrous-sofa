module

public import AmbidextrousSofa.Analysis.TiltedEnergyBarrier
public import AmbidextrousSofa.Analysis.TiltedEndpointBounds

@[expose] public section

/-!
# Actual parameter regions for first-wing unit curvature

Endpoint pressure and the literal middle niche bounds supply the scalar
initial-floor conditions in the small-width, high-tilt, and dry-left
middle-tilt regions. The final application selects the actual sharp
curvature density and derives the slope and initial visibility margin
from the two middle heights.
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
  have hEP := (hU.tilted_endpoint_laws hl hr hheight haffine hlow hhigh).1
  unfold Analysis.tiltedEndpointMomentum
  linarith only [hEP]

theorem IsFullCapMaximizer.initial_floor_conditions_of_small_width
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 2 / 3 ≤ C) (hC1 : C ≤ 18 / 25)
    (hh0 : 3 / 100 ≤ h) (hh1 : h ≤ 17 / 50) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1) :
    Analysis.InitialFloorEnergyConditions (3 * C)
      (capRoof U (horizontalRight U) - 1 + h) h := by
  rw [hU.tilted_endpoint_momentum_eq hl hr hheight haffine hlow hhigh]
  have hn := hU.isCap.middle_niche_le_box_height_of_endpoints hl hr
    (by linarith only [hC0]) (by linarith only [hC1])
  exact Analysis.initialFloorEnergyConditions_small_width_of_endpoint_box hC0 hC1 hh0 hh1
    (sweptNiche_nonneg U (Real.pi / 2) C) hn.2
    (sweptNiche_nonneg U (Real.pi / 2) (-C)) hn.1

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
  exact Analysis.initialFloorEnergyConditions_high_tilt_of_endpoint_box hC0 hC1 hh0 hh1
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
  exact Analysis.initialFloorEnergyConditions_middle_tilt_low_width_of_endpoint_box
    hC0 hC1 hh0 hh1 (sweptNiche_nonneg U (Real.pi / 2) C) hn.2

/-- This actual application has no density, phase, or visibility
hypothesis. The two scalar energy conditions can be supplied by any of
the actual region theorems above or by the refined ordinary-area test. -/
theorem IsFullCapMaximizer.exists_tilted_first_unit_density_of_initial_floor_conditions
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50)
    (hh0 : 0 < h) (hh1 : h < 17 / 50) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hhigh : capRoof U C = 1) (hlow : capRoof U (-C) = 1 - h)
    (hconditions : Analysis.InitialFloorEnergyConditions (3 * C)
      (capRoof U (horizontalRight U) - 1 + h) h) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ sourceKappa (upperCornerVelocity U t)) ∧
      (∀ t, ρ t ≤ 4 * (|horizontalLeft U| + |horizontalRight U| + 1) + 10) ∧
      (upperCurvature U).restrict (regularCurvatureDomain m) =
        (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)) ∧
      (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1) := by
  have hmid : middleHalfInterval (horizontalLeft U) (horizontalRight U) = Icc (-C) C := by
    rw [middleHalfInterval, hl, hr]
    congr 1 <;> ring
  have haff := haffine
  rw [hmid] at haff
  have hleft := haff (-C) ⟨le_rfl, by linarith only [hC0]⟩
  have hright := haff C ⟨by linarith only [hC0], le_rfl⟩
  rw [hlow] at hleft
  rw [hhigh] at hright
  have hmEq : m = h / (2 * C) := (eq_div_iff
    (show 2 * C ≠ 0 by linarith only [hC0])).mpr (by nlinarith only [hleft, hright])
  have hmpos : 0 < m := by rw [hmEq]; exact div_pos hh0 (by linarith only [hC0])
  have hsmall : C + m < 1 := by
    rw [hmEq]
    exact canonical_width_add_slope_lt_one hC0.le hC1 hh1
  obtain ⟨ρ, hρ, hbounds, hcoarse, heq, _⟩ :=
    hU.curvature_density_corner_controls hheight haffine
  have hunit := fullTiltedSupportQuarterPair_ae_first_le_one_of_initial_floor_conditions
    hU hmpos.le haffine hρ (fun t => (hbounds t).1) hcoarse heq
    hl hr hC0 hmpos hsmall hh0 hheight hhigh hlow (fun t => (hbounds t).2) hconditions
  exact ⟨ρ, hρ, hbounds, hcoarse, heq, hunit⟩

end AmbidextrousSofa
