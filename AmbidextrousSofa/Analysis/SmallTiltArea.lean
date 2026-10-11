module

public import AmbidextrousSofa.Analysis.SmallTiltScalar
public import AmbidextrousSofa.Analysis.SplitWingChord
public import AmbidextrousSofa.Analysis.TiltedLeakageMoment
public import AmbidextrousSofa.Analysis.TiltedEndpointBounds
public import AmbidextrousSofa.Analysis.CanonicalOneTurn

@[expose] public section

/-!
# The actual ordinary-area comparison for small positive tilts

The exact survivor identity pays only the actual right-wing outside
niche, since the left-wing convex niche has zero endpoints. The three
selected-polygon chords retain the top overhang. Their common tangent
and the actual endpoint pressures supply the scalar small-height proof.
No area estimate or wing-length identity is supplied as an assumption
to the final geometric theorem in this file.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

namespace Analysis

theorem smallTilt_rational_area_lower {C h z T J P V : ℝ}
    (hC : C ≤ 37 / 50) (hh : 0 ≤ h) (hz : 0 ≤ z) (hT : 0 ≤ T)
    (hzT : z ≤ (10 / 9) * T) (hJ : J ≤ 1 / 40)
    (hchord : T + Real.sqrt ((C - T) ^ 2 + (1 / 2 - h / 4 - 3 * z / 4) ^ 2) +
      Real.sqrt (C ^ 2 + (1 / 2 - h / 4 + z / 4) ^ 2) ≤ 2 * P)
    (harea : P + C * (2 - h) - (T + J) * z / 2 ≤ V) :
    smallTiltBaseline + (2 + smallTiltTangent) * (C - smallTiltWidth) -
      (8871 / 10000) * h - (1839 / 25000) * z - T * z / 2 ≤ V := by
  have hb := smallTilt_vertical_and_overhang_bounds
  linarith only [smallTilt_tangent_le_norm (C - T) (1 / 2 - h / 4 - 3 * z / 4),
    smallTilt_tangent_le_norm C (1 / 2 - h / 4 + z / 4), hchord, harea, hzT,
    smallTilt_baseline_rewrite C, mul_le_mul_of_nonneg_right hC hh,
    mul_le_mul_of_nonneg_right hb.2.1.le hh, mul_le_mul_of_nonneg_right hb.2.1.le hz,
    mul_le_mul_of_nonneg_right hb.2.2.le hT, mul_le_mul_of_nonneg_right hJ hz]

end Analysis

/-- The actual cap, ordinary survivor, source density and support endpoint
produce both initial-floor inequalities. The remaining projection and
early-excess inputs are individual geometric facts, not an assumed score
bound, unit-curvature certificate, or cap classification. -/
theorem IsFullCapMaximizer.smallTilt_initialFloorEnergyConditions_of_actual_geometry
    {U : Set Plane} (hU : IsFullCapMaximizer U)
    {C h T m c K : ℝ} {ρ : ℝ → ℝ} {S : Set ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 2 / 3 ≤ C) (hC1 : C ≤ 37 / 50)
    (hh0 : 0 < h) (hh1 : h ≤ 509 / 10000) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1)
    (hnzero : sweptNiche U (Real.pi / 2) (-C) = 0) (hT : 0 ≤ T)
    (htop : MovingSofaOptimality.vminus U (Real.pi / 2) = (C + T, 1))
    (hTs : T ≤ Analysis.initialFloorSine h)
    (hzT : sweptNiche U (Real.pi / 2) C ≤ (10 / 9) * T)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hsub : Ioo (0 : ℝ) (Real.pi / 2) ⊆ S)
    (hJ : firstExcessMoment ρ ≤ 1 / 40) :
    Analysis.InitialFloorEnergyConditions (3 * C)
      (capRoof U (horizontalRight U) - 1 + h) h := by
  have hC : 0 < C := by linarith only [hC0]
  have hChalf : 1 / 2 ≤ C := by linarith only [hC0]
  have hhmax : h ≤ 17 / 50 := by linarith only [hh1]
  have hAff : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval
      (horizontalLeft U) (horizontalRight U), capRoof U x = m * x + c :=
    ⟨m, c, by simpa only [middleHalfInterval_eq_centered hl hr] using haffine⟩
  have hfit := hU.sweptNiche_le_roof_of_canonical_range hl hr hlow hhigh hChalf hC1
    hh0.le hhmax hheight hAff
  -- The ordinary area: the dry left wing pays nothing and the right wing an excess triangle.
  have harea := hU.isCap.volumeReal_oneTurnSurvivor_eq_centered_integrals hl hr hfit
  rw [hU.isCap.middle_roof_integral_of_affine hC hlow hhigh ⟨m, c, haffine⟩] at harea
  have hL := ConvexOn.integral_le_trapezoid (hU.isCap.convexOn_sweptNiche_wings_of_roof_endpoints
    hl hr hlow hhigh hChalf hC1 hhmax).1 (by linarith only [hC] : -2 * C < -C)
    (hU.isCap.continuous_sweptNiche_pi_div_two.intervalIntegrable _ _)
  rw [hU.isCap.sweptNiche_eq_zero_of_le_left hl.ge, hnzero] at hL
  have hR := hU.isCap.right_niche_integral_le_excess_triangle hρ hρ0 hρK heq hsub htop hC.le
    (le_add_of_nonneg_right hT) fun t ht =>
      (hU.isCap.attachedCorner_fst_mem_middle_of_roof_endpoints hl hr hlow hhigh hChalf hC1
        hhmax ht).2.le
  -- The three chords, with the actual endpoint heights.
  have htoproof : capRoof U (C + T) = 1 := le_antisymm
    (capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _) (le_capRoof hU.isCap.isCompact
      (htop ▸ (MovingSofaOptimality.vminus_mem_edge hU.isCap.imported_isConvexBody _).1))
  have hchord := hU.split_wing_chords_le_twice_score hl hr hC hT
    (by linarith only [hTs, (Analysis.smallTilt_sine_bounds hh0 hh1).2.1, hC0]) hlow hhigh
    htoproof hheight hAff
  have hEP := hU.tilted_endpoint_laws hl hr hheight haffine hlow hhigh
  rw [show 1 - capRoof U (horizontalRight U) =
      1 / 2 - h / 4 - 3 * sweptNiche U (Real.pi / 2) C / 4 by linarith only [hEP.1, hnzero],
    show 1 - h - capRoof U (horizontalLeft U) =
      1 / 2 - h / 4 + sweptNiche U (Real.pi / 2) C / 4 by linarith only [hEP.2, hnzero]] at hchord
  have hlower := Analysis.smallTilt_rational_area_lower (V := volume.real (oneTurnSurvivor U))
    hC1 hh0.le (sweptNiche_nonneg _ _ _) hT hzT hJ hchord (by linarith only [harea, hL, hR])
  have hz1 : sweptNiche U (Real.pi / 2) C ≤ 33 / 100 :=
    (hU.isCap.middle_niche_le_box_height_of_endpoints hl hr hC.le (by linarith only [hC1])).2.trans
      (Analysis.tiltedBoxHeight_lt_thirty_three_hundredths hC.le hC1).le
  convert Analysis.smallTilt_initialFloorEnergyConditions_of_area hC0 hC1 hh0 hh1
    (sweptNiche_nonneg _ _ _) hz1 hTs hzT (hU.isCap.volumeReal_oneTurnSurvivor_le hfit) hlower
    using 2
  unfold Analysis.tiltedEndpointMomentum
  linarith only [hEP.1, hnzero]

end AmbidextrousSofa
