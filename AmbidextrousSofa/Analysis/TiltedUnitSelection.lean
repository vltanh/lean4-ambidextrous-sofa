module

public import AmbidextrousSofa.Analysis.TiltedTopOverhang
public import AmbidextrousSofa.Analysis.SmallTiltArea
public import AmbidextrousSofa.Analysis.TiltedInitialUnitRegions
public import AmbidextrousSofa.Analysis.TiltedTriangleArea
public import AmbidextrousSofa.Analysis.TiltedLateExcess

@[expose] public section

/-!
# First-wing unit density in every remaining actual tilted region

Small widths satisfy the initial-floor test directly. At larger widths,
the actual dry endpoint and top projection supply the small-height area
comparison. The remaining height ranges satisfy the established energy
tests or contradict the actual three-angle triangle estimate. The final
selector has only the centered canonical cap hypotheses and selects its
density from the cap itself.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

/-- Actual first-unit density throughout the remaining tilted canonical
range. Every scalar region, projection, reflected excess, and area input
has been discharged from the cap itself. -/
theorem IsFullCapMaximizer.exists_tilted_first_unit_density
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C < 37 / 50) (hh0 : 0 < h) (hh1 : h < 17 / 50)
    (hm : 0 < m) (hsmall : C + m < 1) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hhigh : capRoof U C = 1) (hlow : capRoof U (-C) = 1 - h) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ sourceKappa (upperCornerVelocity U t)) ∧
      (∀ t, ρ t ≤ 4 * (|horizontalLeft U| + |horizontalRight U| + 1) + 10) ∧
      (upperCurvature U).restrict (regularCurvatureDomain m) =
        (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)) ∧
      (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1) := by
  have haff : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c := by
    simpa only [middleHalfInterval_eq_centered hl hr] using haffine
  obtain ⟨ρ, hρ, hbounds, hcoarse, heq, -⟩ := hU.curvature_density_corner_controls hheight haffine
  have hρ0 (t : ℝ) := (hbounds t).1
  refine ⟨ρ, hρ, hbounds, hcoarse, heq,
    fullTiltedSupportQuarterPair_ae_first_le_one_of_initial_floor_conditions hU hm.le haffine hρ
      hρ0 hcoarse heq hl hr hC0 hm hsmall hh0 hheight hhigh hlow (fun t => (hbounds t).2) ?_⟩
  by_cases hCsmall : C ≤ 2 / 3
  · -- Small widths pass the initial-floor test directly.
    have he0 := capRoof_nonneg hU.isCap.isCompact
      (fun p hp => (hU.isCap.inStrip hp).1) (horizontalRight U)
    have he1 := capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip (horizontalRight U)
    have hhs : h ≤ Analysis.initialFloorSine h := Real.le_sqrt_of_sq_le
      (by linarith only [mul_nonneg hh0.le (by linarith only [hh1] : (0 : ℝ) ≤ 1 - h)])
    have hC2 := mul_nonneg (sub_nonneg.2 hCsmall) (by linarith only [hC0] : (0 : ℝ) ≤ 2 / 3 + C)
    unfold Analysis.InitialFloorEnergyConditions
    constructor
    · linarith only [hC2, mul_nonneg (add_nonneg he0 hh0.le)
        (by linarith only [he1, hh1] : 0 ≤ 2 - capRoof U (horizontalRight U) - h)]
    · linarith only [hC2, mul_nonneg he0 (sub_nonneg.2 he1), mul_nonneg hh0.le (sub_nonneg.2 he1),
        hhs, mul_nonneg (by linarith only [hC0] : (0 : ℝ) ≤ 3 * C - 1)
          (Analysis.initialFloorSine_nonneg h)]
  replace hC0 : 2 / 3 < C := lt_of_not_ge hCsmall
  obtain ⟨hT, hdry, hTs⟩ :=
    hU.tilted_dry_left_and_overhang_bounds hl hr hC0.le hC1.le hh0 hh1 hheight haff hlow hhigh
  by_cases hhsmall : h ≤ 509 / 10000
  · -- Small heights: the dry endpoint and the top projection give the area comparison.
    obtain ⟨hlate, hJ⟩ := fullTiltedSupportQuarterPair_late_unit_and_excess_moment hU hm.le
      haffine hρ hρ0 hcoarse heq hl hr hC0 hC1 hm hsmall hh0 hh1 hheight hhigh hlow
      (fun t => (hbounds t).2)
    have htop : MovingSofaOptimality.vminus U (Real.pi / 2) =
        (C + ((MovingSofaOptimality.vminus U (Real.pi / 2)).1 - C), 1) :=
      Prod.ext (by ring) ((top_vminus_snd_eq_capHeight U).trans hheight)
    have hsub := firstQuarter_subset_regularCurvatureDomain_of_nonneg hm.le
    have hn := hU.isCap.middle_niche_le_top_overhang_of_late_unit hρ hρ0 hcoarse heq hsub hr
      (by linarith only [hC0]) hC1.le (by linarith only [hT]) htop hlate
    refine hU.smallTilt_initialFloorEnergyConditions_of_actual_geometry hl hr hC0.le hC1.le hh0
      hhsmall hheight haff hlow hhigh hdry hT.le htop hTs (hn.trans ?_) hρ hρ0 hcoarse heq hsub
      hJ.le
    have hsq : 9 * C / 10 ≤ Real.sqrt (1 - C ^ 2) :=
      Real.le_sqrt_of_sq_le (by nlinarith only [hC0, hC1])
    rw [div_le_iff₀ ((by linarith only [hC0] : (0 : ℝ) < 9 * C / 10).trans_le hsq)]
    linarith only [mul_le_mul_of_nonneg_left hsq hT.le]
  by_cases hhhigh : 21 / 100 ≤ h
  · exact hU.initial_floor_conditions_of_high_tilt hl hr hC0.le hC1.le hhhigh hh1.le hm.le hheight
      haff hlow hhigh
  by_cases hCmiddle : C ≤ 73 / 100
  · exact hU.initial_floor_conditions_of_middle_tilt_low_width hl hr hC0.le hCmiddle
      (by linarith only [hhsmall]) (le_of_not_ge hhhigh) hheight haff hlow hhigh hdry
  -- The middle heights at large widths contradict the actual triangle score estimate.
  have e1 : -(2 * C) / 2 = -C := by ring
  have e2 : 2 * C / 2 = C := by ring
  exact (hU.false_of_medium_tilt_large_width_zero_left (a := 2 * C) (by linarith only [hCmiddle])
    (by linarith only [hC1]) (by linarith only [hhsmall]) (le_of_not_ge hhhigh)
    (hl.trans (neg_mul 2 C)) hr hheight (by rwa [e1]) (by rwa [e2]) ⟨m, c, by rwa [e1, e2]⟩
    (by rwa [e1])).elim

end AmbidextrousSofa
