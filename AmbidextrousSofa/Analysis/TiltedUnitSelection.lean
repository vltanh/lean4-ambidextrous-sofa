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
selector has only the centered canonical cap hypotheses.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

namespace Analysis

theorem initialFloorEnergyConditions_of_span_le_two {d e h : ℝ}
    (hd0 : 1 ≤ d) (hd1 : d ≤ 2) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    InitialFloorEnergyConditions d (e - 1 + h) h := by
  let B := e - 1 + h
  have hB0 : -1 ≤ B := by dsimp only [B]; linarith only [he0, hh0]
  have hB1 : B ≤ 1 := by dsimp only [B]; linarith only [he1, hh1]
  have hBsq : B ^ 2 ≤ 1 := by
    have hp := mul_nonneg (show 0 ≤ B + 1 by linarith only [hB0]) (sub_nonneg.mpr hB1)
    nlinarith only [hp]
  have hdsq : d ^ 2 ≤ 4 := by
    have hp := mul_nonneg (sub_nonneg.mpr hd1)
      (show 0 ≤ 2 + d by linarith only [hd0])
    nlinarith only [hp]
  have hs0 := initialFloorSine_nonneg h
  have hssq := initialFloorSine_sq hh0 (by linarith only [hh1])
  have hhs : h ≤ initialFloorSine h := by
    apply (sq_le_sq₀ hh0 hs0).mp
    nlinarith only [hssq, mul_nonneg hh0 (sub_nonneg.mpr hh1)]
  have hds : initialFloorSine h ≤ d * initialFloorSine h := by
    have hp := mul_nonneg (sub_nonneg.mpr hd0) hs0
    nlinarith only [hp]
  have hBe : B * e ≤ d * initialFloorSine h := by
    by_cases hB : B ≤ 0
    · exact (mul_nonpos_of_nonpos_of_nonneg hB he0).trans
        (mul_nonneg (by linarith only [hd0]) hs0)
    · have hBe : B * e ≤ B := by
        have hp := mul_le_mul_of_nonneg_left he1 (le_of_not_ge hB)
        simpa only [mul_one] using hp
      have hBh : B ≤ h := by dsimp only [B]; linarith only [he1]
      exact hBe.trans (hBh.trans (hhs.trans hds))
  change d ^ 2 + B ^ 2 ≤ 5 ∧
    d ^ 2 + B ^ 2 + B * (1 - h) - d * initialFloorSine h ≤ 4
  constructor
  · linarith only [hdsq, hBsq]
  · have hBidentity : B ^ 2 + B * (1 - h) = B * e := by dsimp only [B]; ring
    rw [show d ^ 2 + B ^ 2 + B * (1 - h) = d ^ 2 + (B ^ 2 + B * (1 - h)) by ring,
      hBidentity]
    linarith only [hdsq, hBe]

theorem width_over_circleHeight_le_ten_ninths {C : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 37 / 50) :
    C / Real.sqrt (1 - C ^ 2) ≤ 10 / 9 := by
  have hCsq : C ^ 2 ≤ (37 / 50 : ℝ) ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hC1)
      (show 0 ≤ 37 / 50 + C by linarith only [hC0])
    nlinarith only [hp]
  have hrad : 0 < 1 - C ^ 2 := by linarith only [hCsq]
  have hr := Real.sqrt_pos.mpr hrad
  have hrsq := Real.sq_sqrt hrad.le
  have hsq : (9 * C) ^ 2 ≤ (10 * Real.sqrt (1 - C ^ 2)) ^ 2 := by
    nlinarith only [hCsq, hrsq]
  have hle := (sq_le_sq₀ (show 0 ≤ 9 * C by positivity)
    (show 0 ≤ 10 * Real.sqrt (1 - C ^ 2) by positivity)).mp hsq
  apply (div_le_iff₀ hr).mpr
  linarith only [hle]

end Analysis

theorem IsFullCapMaximizer.initial_floor_conditions_of_width_le_two_thirds
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h : ℝ}
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 2 / 3) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    Analysis.InitialFloorEnergyConditions (3 * C)
      (capRoof U (horizontalRight U) - 1 + h) h := by
  have he0 := capRoof_nonneg hU.isCap.isCompact
    (fun p hp => (hU.isCap.inStrip hp).1) (horizontalRight U)
  have he1 := capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip (horizontalRight U)
  exact Analysis.initialFloorEnergyConditions_of_span_le_two
    (by linarith only [hC0]) (by linarith only [hC1]) he0 he1 hh0 hh1

/-- The forward actual excess selector and literal top trace supply
the right endpoint niche bound used by the small-height region. -/
theorem IsFullCapMaximizer.tilted_middle_niche_le_ten_ninths_overhang
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 2 / 3 < C) (hC1 : C < 37 / 50) (hh0 : 0 < h) (hh1 : h < 17 / 50)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1) :
    sweptNiche U (Real.pi / 2) C ≤
      (10 / 9) * ((MovingSofaOptimality.vminus U (Real.pi / 2)).1 - C) := by
  have hm := positive_affine_slope_of_middle_heights (by linarith only [hC0]) hh0
    haffine hlow hhigh
  have haff : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c := by
    simpa only [middleHalfInterval_eq_centered hl hr] using haffine
  obtain ⟨ρ, hρ, hbounds, hcoarse, heq, hlate, _hJ⟩ :=
    hU.exists_tilted_first_density_with_late_controls
      hl hr hC0 hC1 hh0 hh1 hheight haff hhigh hlow
  have hT := hU.tilted_top_overhang_pos hl hr hC0.le hC1.le hh0 hh1 hheight haffine hlow hhigh
  have htop : MovingSofaOptimality.vminus U (Real.pi / 2) =
      ((MovingSofaOptimality.vminus U (Real.pi / 2)).1, (1 : ℝ)) :=
    Prod.ext rfl ((top_vminus_snd_eq_capHeight U).trans hheight)
  have hn := hU.isCap.middle_niche_le_top_overhang_of_late_unit hρ
    (fun s => (hbounds s).1) hcoarse heq
    (firstQuarter_subset_regularCurvatureDomain_of_nonneg hm.le) hr
    (by linarith only [hC0]) hC1.le (by linarith only [hT]) htop hlate
  have hlam := mul_le_mul_of_nonneg_left
    (Analysis.width_over_circleHeight_le_ten_ninths (by linarith only [hC0]) hC1.le) hT.le
  have hlam' : ((MovingSofaOptimality.vminus U (Real.pi / 2)).1 - C) * C /
      Real.sqrt (1 - C ^ 2) ≤ (10 / 9) * ((MovingSofaOptimality.vminus U (Real.pi / 2)).1 - C) := by
    rw [mul_div_assoc, mul_comm (10 / 9 : ℝ)]
    exact hlam
  exact hn.trans hlam'

/-- The small-height scalar test now has no external projection,
excess, endpoint niche, or ordinary-area assumptions. -/
theorem IsFullCapMaximizer.smallTilt_initial_floor_conditions
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 2 / 3 < C) (hC1 : C < 37 / 50)
    (hh0 : 0 < h) (hh1 : h ≤ 509 / 10000) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1) :
    Analysis.InitialFloorEnergyConditions (3 * C)
      (capRoof U (horizontalRight U) - 1 + h) h := by
  let T := (MovingSofaOptimality.vminus U (Real.pi / 2)).1 - C
  have hhmax : h < 17 / 50 := by linarith only [hh1]
  have hm := positive_affine_slope_of_middle_heights (by linarith only [hC0]) hh0
    haffine hlow hhigh
  have haff : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c := by
    simpa only [middleHalfInterval_eq_centered hl hr] using haffine
  obtain ⟨hT, hdry, _hTeq, hTs, _hTeL, _hTaxis⟩ :=
    hU.tilted_dry_left_and_overhang_bounds
      hl hr hC0.le hC1.le hh0 hhmax hheight haffine hlow hhigh
  obtain ⟨ρ, hρ, hbounds, hcoarse, heq, _hlate, hJ⟩ :=
    hU.exists_tilted_first_density_with_late_controls
      hl hr hC0 hC1 hh0 hhmax hheight haff hhigh hlow
  have hzT := hU.tilted_middle_niche_le_ten_ninths_overhang
    hl hr hC0 hC1 hh0 hhmax hheight haffine hlow hhigh
  have htop : MovingSofaOptimality.vminus U (Real.pi / 2) = (C + T, (1 : ℝ)) := by
    apply Prod.ext
    · dsimp only [T]
      ring
    · exact (top_vminus_snd_eq_capHeight U).trans hheight
  exact hU.smallTilt_initialFloorEnergyConditions_of_actual_geometry
    hl hr hC0.le hC1.le hh0 hh1 hheight haffine hlow hhigh hdry hT.le htop
    hTs hzT hρ (fun s => (hbounds s).1) hcoarse heq
    (firstQuarter_subset_regularCurvatureDomain_of_nonneg hm.le) hJ.le

/-- Every remaining canonical tilted maximum passes the initial-floor
energy criterion. The middle high-width branch is eliminated by its
actual triangle score estimate. -/
theorem IsFullCapMaximizer.tilted_initial_floor_conditions
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C < 37 / 50) (hh0 : 0 < h) (hh1 : h < 17 / 50)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hlow : capRoof U (-C) = 1 - h) (hhigh : capRoof U C = 1) :
    Analysis.InitialFloorEnergyConditions (3 * C)
      (capRoof U (horizontalRight U) - 1 + h) h := by
  by_cases hCsmall : C ≤ 2 / 3
  · exact hU.initial_floor_conditions_of_width_le_two_thirds hC0 hCsmall hh0.le
      (by linarith only [hh1])
  have hCbig : 2 / 3 < C := lt_of_not_ge hCsmall
  by_cases hhsmall : h ≤ 509 / 10000
  · exact hU.smallTilt_initial_floor_conditions
      hl hr hCbig hC1 hh0 hhsmall hheight haffine hlow hhigh
  have hm := positive_affine_slope_of_middle_heights (by linarith only [hC0]) hh0
    haffine hlow hhigh
  by_cases hhhigh : 21 / 100 ≤ h
  · exact hU.initial_floor_conditions_of_high_tilt
      hl hr hCbig.le hC1.le hhhigh hh1.le hm.le hheight haffine hlow hhigh
  have hhmiddle : 1 / 20 ≤ h := by linarith only [lt_of_not_ge hhsmall]
  have hhmiddle' : h ≤ 21 / 100 := (lt_of_not_ge hhhigh).le
  have hdry := (hU.tilted_dry_left_and_overhang_bounds
    hl hr hCbig.le hC1.le hh0 hh1 hheight haffine hlow hhigh).2.1
  by_cases hCmiddle : C ≤ 73 / 100
  · exact hU.initial_floor_conditions_of_middle_tilt_low_width
      hl hr hCbig.le hCmiddle hhmiddle hhmiddle' hheight haffine hlow hhigh hdry
  exfalso
  apply hU.false_of_medium_tilt_large_width_zero_left
    (a := 2 * C) (h := h)
    (by linarith only [lt_of_not_ge hCmiddle]) (by linarith only [hC1]) hhmiddle hhmiddle'
    (by simpa only [neg_mul] using hl) hr hheight
  · simpa only [show -(2 * C) / 2 = -C by ring] using hlow
  · simpa only [show 2 * C / 2 = C by ring] using hhigh
  · refine ⟨m, c, ?_⟩
    simpa only [show -(2 * C) / 2 = -C by ring, show 2 * C / 2 = C by ring] using haffine
  · simpa only [show -(2 * C) / 2 = -C by ring] using hdry

/-- Actual first-unit density throughout the remaining tilted canonical
range. Every scalar region, projection, reflected excess, and area input
has been discharged from the cap itself. -/
theorem IsFullCapMaximizer.exists_tilted_first_unit_density
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C < 37 / 50) (hh0 : 0 < h) (hh1 : h < 17 / 50)
    (hheight : capHeight U = 1)
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
  exact hU.exists_tilted_first_unit_density_of_initial_floor_conditions
    hl hr hC0 hC1.le hh0 hh1 hheight haffine hhigh hlow
    (hU.tilted_initial_floor_conditions hl hr hC0 hC1 hh0 hh1 hheight haff hlow hhigh)

end AmbidextrousSofa
