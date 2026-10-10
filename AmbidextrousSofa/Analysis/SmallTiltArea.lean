import AmbidextrousSofa.Analysis.SmallTiltScalar
import AmbidextrousSofa.Analysis.SplitWingChord
import AmbidextrousSofa.Analysis.TiltedLeakageMoment
import AmbidextrousSofa.Analysis.TiltedEndpointBounds
import AmbidextrousSofa.Analysis.CanonicalOneTurn

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
  have hR := smallTilt_tangent_le_norm (C - T) (1 / 2 - h / 4 - 3 * z / 4)
  have hL := smallTilt_tangent_le_norm C (1 / 2 - h / 4 + z / 4)
  have hsharp : smallTiltBaseline + (2 + smallTiltTangent) * (C - smallTiltWidth) -
      C * h - (smallTiltVertical / 4) * (h + z) +
      ((1 - smallTiltTangent) / 2) * T - (T + J) * z / 2 ≤ V := by
    nlinarith only [hR, hL, hchord, harea, smallTilt_baseline_rewrite C]
  have hc := mul_le_mul_of_nonneg_right hC hh
  have hmh := mul_le_mul_of_nonneg_right smallTilt_vertical_and_overhang_bounds.2.1.le hh
  have hmz := mul_le_mul_of_nonneg_right smallTilt_vertical_and_overhang_bounds.2.1.le hz
  have hat := mul_le_mul_of_nonneg_right smallTilt_vertical_and_overhang_bounds.2.2.le hT
  have hzt : (9 / 10) * z ≤ T := by linarith only [hzT]
  have hzpay := mul_le_mul_of_nonneg_left hzt (show (0 : ℝ) ≤ 956 / 10000 by norm_num)
  have hj := mul_le_mul_of_nonneg_right hJ hz
  nlinarith only [hsharp, hc, hmh, hmz, hat, hzpay, hj]

end Analysis

theorem IsFullCapMaximizer.ordinary_area_ge_score_of_dry_left_and_excess
    {U : Set Plane} (hU : IsFullCapMaximizer U)
    {C h T m c K : ℝ} {ρ : ℝ → ℝ} {S : Set ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 37 / 50) (hh0 : 0 ≤ h) (hh1 : h ≤ 17 / 50)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1)
    (hnzero : sweptNiche U (Real.pi / 2) (-C) = 0) (hT : 0 ≤ T)
    (htop : Imported.vminus U (Real.pi / 2) = (C + T, 1))
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hsub : Ioo (0 : ℝ) (Real.pi / 2) ⊆ S) :
    capScore U (Real.pi / 2) + C * (2 - h) -
      (T + firstExcessMoment ρ) * sweptNiche U (Real.pi / 2) C / 2 ≤
        volume.real (oneTurnSurvivor U) := by
  have hAff : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval
      (horizontalLeft U) (horizontalRight U), capRoof U x = m * x + c :=
    ⟨m, c, by simpa only [middleHalfInterval_eq_centered hl hr] using haffine⟩
  have hfit := hU.sweptNiche_le_roof_of_canonical_range
    hl hr hlow hhigh hC0 hC1 hh0 hh1 hheight hAff
  have harea := hU.isCap.volumeReal_oneTurnSurvivor_eq_centered_integrals hl hr hfit
  rw [hU.isCap.middle_roof_integral_of_affine (by linarith only [hC0])
    hlow hhigh ⟨m, c, haffine⟩] at harea
  have hconv := (hU.isCap.convexOn_sweptNiche_wings_of_roof_endpoints
    hl hr hlow hhigh hC0 hC1 hh1).1
  have hzeroL : sweptNiche U (Real.pi / 2) (-2 * C) = 0 := by
    rw [← hl]
    exact hU.isCap.sweptNiche_eq_zero_of_le_left le_rfl
  have hL := hconv.integral_le_trapezoid (show -2 * C < -C by linarith only [hC0])
    (hU.isCap.continuous_sweptNiche_pi_div_two.intervalIntegrable _ _)
  rw [hzeroL, hnzero, add_zero, mul_zero, zero_div] at hL
  have hcorner : ∀ t ∈ Ioo (0 : ℝ) (Real.pi / 2), (attachedCorner U t).1 ≤ C :=
    fun t ht => (hU.isCap.attachedCorner_fst_mem_middle_of_roof_endpoints
      hl hr hlow hhigh hC0 hC1 hh1 ht).2.le
  have hR := hU.isCap.right_niche_integral_le_excess_triangle hρ hρ0 hρK heq hsub htop
    (show 0 ≤ C by linarith only [hC0]) (show C ≤ C + T by linarith only [hT]) hcorner
  nlinarith only [harea, hL, hR]

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
    (htop : Imported.vminus U (Real.pi / 2) = (C + T, 1))
    (hTs : T ≤ Analysis.initialFloorSine h)
    (hzT : sweptNiche U (Real.pi / 2) C ≤ (10 / 9) * T)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hsub : Ioo (0 : ℝ) (Real.pi / 2) ⊆ S)
    (hJ : firstExcessMoment ρ ≤ 1 / 40) :
    Analysis.InitialFloorEnergyConditions (3 * C)
      (capRoof U (horizontalRight U) - 1 + h) h := by
  let z := sweptNiche U (Real.pi / 2) C
  have hz0 : 0 ≤ z := sweptNiche_nonneg _ _ _
  have hAff : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval
      (horizontalLeft U) (horizontalRight U), capRoof U x = m * x + c :=
    ⟨m, c, by simpa only [middleHalfInterval_eq_centered hl hr] using haffine⟩
  have hChalf : 1 / 2 ≤ C := by linarith only [hC0]
  have hhmax : h ≤ 17 / 50 := by linarith only [hh1]
  have hfit := hU.sweptNiche_le_roof_of_canonical_range
    hl hr hlow hhigh hChalf hC1 hh0.le hhmax hheight hAff
  have hV := hU.isCap.volumeReal_oneTurnSurvivor_le hfit
  have hs := Analysis.smallTilt_sine_bounds hh0 hh1
  have hTC : T < C := by linarith only [hTs, hs.2.1, hC0]
  have htopmem : (C + T, (1 : ℝ)) ∈ U := by
    rw [← htop]
    exact (Imported.vminus_mem_edge hU.isCap.imported_isConvexBody (Real.pi / 2)).1
  have htoproof : capRoof U (C + T) = 1 := le_antisymm
    (capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _)
    (le_capRoof hU.isCap.isCompact htopmem)
  have hchord := hU.split_wing_chords_le_twice_score hl hr
    (by linarith only [hC0]) hT hTC hlow hhigh htoproof hheight hAff
  have hEP := hU.tilted_endpoint_laws hl hr hheight haffine hlow hhigh
  have hrightdrop : 1 - capRoof U (horizontalRight U) = 1 / 2 - h / 4 - 3 * z / 4 := by
    dsimp only [z]
    linarith only [hEP.1, hnzero]
  have hleftdrop : 1 - h - capRoof U (horizontalLeft U) = 1 / 2 - h / 4 + z / 4 := by
    dsimp only [z]
    linarith only [hEP.2, hnzero]
  rw [hrightdrop, hleftdrop] at hchord
  have harea := hU.ordinary_area_ge_score_of_dry_left_and_excess
    hl hr hChalf hC1 hh0.le hhmax hheight haffine hlow hhigh hnzero hT htop
    hρ hρ0 hρK heq hsub
  have hlower := Analysis.smallTilt_rational_area_lower hC1 hh0.le hz0 hT hzT hJ hchord harea
  have hbox := (hU.isCap.middle_niche_le_box_height_of_endpoints hl hr
    (show 0 ≤ C by linarith only [hC0]) (show C ≤ 1 by linarith only [hC1])).2
  have hH := Analysis.tiltedBoxHeight_lt_thirty_three_hundredths
    (show 0 ≤ C by linarith only [hC0]) hC1
  have hz1 : z ≤ 33 / 100 := by
    dsimp only [z]
    unfold Analysis.tiltedBoxHeight at hH
    linarith only [hbox, hH]
  have hB : capRoof U (horizontalRight U) - 1 + h = Analysis.tiltedEndpointMomentum h z 0 := by
    unfold Analysis.tiltedEndpointMomentum
    dsimp only [z]
    linarith only [hEP.1, hnzero]
  rw [hB]
  exact Analysis.smallTilt_initialFloorEnergyConditions_of_area
    hC0 hC1 hh0 hh1 hz0 hz1 hTs hzT hV hlower

end AmbidextrousSofa
