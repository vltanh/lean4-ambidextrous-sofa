module

public import AmbidextrousSofa.Analysis.NicheFit

@[expose] public section

/-!
# The actual survivor area and the tilted one-turn necessary inequality

Cavalieri identifies the ordinary area with the integral of the actual
nonnegative fiber lengths. The middle affine roof contributes its exact
trapezoid area. Convex wing niches lie below their chords and vanish at
the outer endpoints. These facts give the area comparison with the true
cap score, and therefore the ordinary one-turn necessary inequality.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem IsDownwardCap.volumeReal_oneTurnSurvivor_eq_integral {U : Set Plane}
    (hU : IsDownwardCap U)
    (hfit : ∀ x ∈ horizontalProjection U, sweptNiche U (Real.pi / 2) x ≤ capRoof U x) :
    volume.real (oneTurnSurvivor U) = ∫ x in Icc (horizontalLeft U) (horizontalRight U),
      capRoof U x - sweptNiche U (Real.pi / 2) x := by
  have hregion : oneTurnSurvivor U = verticalIntervalRegion
      (Icc (horizontalLeft U) (horizontalRight U))
      (sweptNiche U (Real.pi / 2)) (capRoof U) := by
    rw [hU.oneTurnSurvivor_eq_verticalIntervalRegion,
      horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
  have hroof := hU.integrableOn_capRoof_Icc (horizontalLeft U) (horizontalRight U)
  have hniche : IntegrableOn (sweptNiche U (Real.pi / 2))
      (Icc (horizontalLeft U) (horizontalRight U)) :=
    hU.continuous_sweptNiche_pi_div_two.integrableOn_Icc
  have hnonneg : ∀ᵐ x ∂volume.restrict (Icc (horizontalLeft U) (horizontalRight U)),
      0 ≤ capRoof U x - sweptNiche U (Real.pi / 2) x := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    apply sub_nonneg.mpr (hfit x _)
    rwa [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
  have hvol := volume_verticalIntervalRegion_eq_lintegral
    (I := Icc (horizontalLeft U) (horizontalRight U)) measurableSet_Icc
    hU.continuous_sweptNiche_pi_div_two.measurable hU.measurable_capRoof
  rw [← hregion] at hvol
  have hof := ofReal_integral_eq_lintegral_ofReal (hroof.sub hniche) hnonneg
  simp only [Pi.sub_apply] at hof
  change (volume (oneTurnSurvivor U)).toReal = _
  rw [hvol, ← hof, ENNReal.toReal_ofReal (integral_nonneg_of_ae hnonneg)]

theorem IsDownwardCap.volumeReal_oneTurnSurvivor_eq_intervalIntegral {U : Set Plane}
    (hU : IsDownwardCap U)
    (hfit : ∀ x ∈ horizontalProjection U, sweptNiche U (Real.pi / 2) x ≤ capRoof U x) :
    volume.real (oneTurnSurvivor U) = ∫ x in horizontalLeft U..horizontalRight U,
      capRoof U x - sweptNiche U (Real.pi / 2) x := by
  rw [hU.volumeReal_oneTurnSurvivor_eq_integral hfit, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact)]

theorem IsDownwardCap.volumeReal_oneTurnSurvivor_eq_score_middle_exterior
    {U : Set Plane} (hU : IsDownwardCap U)
    (hfit : ∀ x ∈ horizontalProjection U, sweptNiche U (Real.pi / 2) x ≤ capRoof U x) :
    volume.real (oneTurnSurvivor U) = capScore U (Real.pi / 2) +
      (∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x) -
      ∫ x in Icc (horizontalLeft U) (horizontalRight U) \
        middleHalfInterval (horizontalLeft U) (horizontalRight U), sweptNiche U (Real.pi / 2) x := by
  have hroof := hU.integrableOn_capRoof_Icc (horizontalLeft U) (horizontalRight U)
  have hniche : IntegrableOn (sweptNiche U (Real.pi / 2))
      (Icc (horizontalLeft U) (horizontalRight U)) :=
    hU.continuous_sweptNiche_pi_div_two.integrableOn_Icc
  have hJI := middleHalfInterval_subset
    (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact)
  have hsplitRoof := setIntegral_sdiff
    (measurableSet_middleHalfInterval (horizontalLeft U) (horizontalRight U)) hroof hJI
  have hsplitNiche := setIntegral_sdiff
    (measurableSet_middleHalfInterval (horizontalLeft U) (horizontalRight U)) hniche hJI
  rw [hU.volumeReal_oneTurnSurvivor_eq_integral hfit,
    integral_sub hroof hniche, hU.capScore_pi_div_two]
  linarith

theorem IsDownwardCap.volumeReal_oneTurnSurvivor_eq_centered_integrals
    {U : Set Plane} (hU : IsDownwardCap U) {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hfit : ∀ x ∈ horizontalProjection U, sweptNiche U (Real.pi / 2) x ≤ capRoof U x) :
    volume.real (oneTurnSurvivor U) = capScore U (Real.pi / 2) +
      (∫ x in (-C)..C, capRoof U x) -
      ((∫ x in (-2 * C)..(-C), sweptNiche U (Real.pi / 2) x) +
        ∫ x in C..(2 * C), sweptNiche U (Real.pi / 2) x) := by
  have hscore := hU.capScore_eq_intervalSpatialScore (Real.pi / 2)
  rw [hl, hr, intervalSpatialScore] at hscore
  have hminus : -2 * C + (2 * C - -2 * C) / 4 = -C := by ring
  have hplus : 2 * C - (2 * C - -2 * C) / 4 = C := by ring
  rw [hminus, hplus] at hscore
  simp_rw [hU.partialBarrier_pi_div_two] at hscore
  have hroofL := hU.intervalIntegrable_capRoof (-2 * C) (-C)
  have hroofM := hU.intervalIntegrable_capRoof (-C) C
  have hroofR := hU.intervalIntegrable_capRoof C (2 * C)
  have hnicheL := hU.continuous_sweptNiche_pi_div_two.intervalIntegrable (μ := volume) (-2 * C) (-C)
  have hnicheM := hU.continuous_sweptNiche_pi_div_two.intervalIntegrable (μ := volume) (-C) C
  have hnicheR := hU.continuous_sweptNiche_pi_div_two.intervalIntegrable (μ := volume) C (2 * C)
  have hroofLM := intervalIntegral.integral_add_adjacent_intervals hroofL hroofM
  have hroofAll := intervalIntegral.integral_add_adjacent_intervals (hroofL.trans hroofM) hroofR
  have hnicheLM := intervalIntegral.integral_add_adjacent_intervals hnicheL hnicheM
  have hnicheAll := intervalIntegral.integral_add_adjacent_intervals (hnicheL.trans hnicheM) hnicheR
  rw [hU.volumeReal_oneTurnSurvivor_eq_intervalIntegral hfit, hl, hr,
    intervalIntegral.integral_sub ((hroofL.trans hroofM).trans hroofR)
      ((hnicheL.trans hnicheM).trans hnicheR)]
  linarith

theorem ConvexOn.le_roofChord {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ConvexOn ℝ s f) {a b x : ℝ} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a < b) (hx : x ∈ Icc a b) : f x ≤ roofChord f a b x := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hsum : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
    field_simp [hba.ne'] <;> ring
  have hpoint : (b - x) / (b - a) * a + (x - a) / (b - a) * b = x := by
    field_simp [hba.ne'] <;> ring
  have h := hf.2 ha hb (div_nonneg (sub_nonneg.mpr hx.2) hba.le)
    (div_nonneg (sub_nonneg.mpr hx.1) hba.le) hsum
  rw [roofChord_eq_interpolation f hab]
  simpa only [smul_eq_mul, hpoint] using h

theorem integral_roofChord (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) :
    (∫ x in a..b, roofChord f a b x) = (b - a) * (f a + f b) / 2 := by
  unfold roofChord
  have hconst : IntervalIntegrable (fun _ : ℝ => f a) volume a b :=
    continuous_const.intervalIntegrable _ _
  have hlin : IntervalIntegrable (fun x : ℝ => (f b - f a) / (b - a) * (x - a)) volume a b :=
    ((continuous_id.sub continuous_const).const_mul _).intervalIntegrable _ _
  have hid : IntervalIntegrable (fun x : ℝ => x) volume a b :=
    continuous_id.intervalIntegrable _ _
  have ha : IntervalIntegrable (fun _ : ℝ => a) volume a b :=
    continuous_const.intervalIntegrable _ _
  rw [intervalIntegral.integral_add hconst hlin,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hid ha, integral_id]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  field_simp [(sub_pos.mpr hab).ne']
  ring

theorem ConvexOn.integral_le_trapezoid {f : ℝ → ℝ} {a b : ℝ}
    (hf : ConvexOn ℝ (Icc a b) f) (hab : a < b)
    (hfi : IntervalIntegrable f volume a b) :
    (∫ x in a..b, f x) ≤ (b - a) * (f a + f b) / 2 := by
  rw [← integral_roofChord f hab]
  apply intervalIntegral.integral_mono_on hab.le hfi
    ((continuous_roofChord f a b).intervalIntegrable a b)
  intro x hx
  exact ConvexOn.le_roofChord hf ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab hx

theorem IsDownwardCap.wing_niche_integrals_le
    {U : Set Plane} (hU : IsDownwardCap U) {C : ℝ} (hC : 0 < C)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hconvL : ConvexOn ℝ (Icc (-2 * C) (-C)) (sweptNiche U (Real.pi / 2)))
    (hconvR : ConvexOn ℝ (Icc C (2 * C)) (sweptNiche U (Real.pi / 2))) :
    (∫ x in (-2 * C)..(-C), sweptNiche U (Real.pi / 2) x) +
      (∫ x in C..(2 * C), sweptNiche U (Real.pi / 2) x) ≤
      C * (sweptNiche U (Real.pi / 2) (-C) + sweptNiche U (Real.pi / 2) C) / 2 := by
  have hzeroL : sweptNiche U (Real.pi / 2) (-2 * C) = 0 := by
    rw [← hl]
    exact hU.sweptNiche_eq_zero_of_le_left le_rfl
  have hzeroR : sweptNiche U (Real.pi / 2) (2 * C) = 0 := by
    rw [← hr]
    exact hU.sweptNiche_eq_zero_of_right_le le_rfl
  have hL := ConvexOn.integral_le_trapezoid hconvL (by linarith)
    (hU.continuous_sweptNiche_pi_div_two.intervalIntegrable _ _)
  have hR := ConvexOn.integral_le_trapezoid hconvR (by linarith)
    (hU.continuous_sweptNiche_pi_div_two.intervalIntegrable _ _)
  rw [hzeroL] at hL
  rw [hzeroR] at hR
  nlinarith

theorem IsDownwardCap.middle_roof_integral_of_affine
    {U : Set Plane} (hU : IsDownwardCap U) {C h : ℝ} (hC : 0 < C)
    (hleft : capRoof U (-C) = 1 - h) (hright : capRoof U C = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c) :
    (∫ x in (-C)..C, capRoof U x) = 2 * C - C * h := by
  obtain ⟨m, c, haffine⟩ := haffine
  have hCC : -C < C := by linarith
  have heq := eqOn_roofChord_of_affine hCC haffine
  calc
    _ = ∫ x in (-C)..C, roofChord (capRoof U) (-C) C x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hCC.le] at hx
      exact heq hx
    _ = 2 * C - C * h := by
      rw [integral_roofChord _ hCC, hleft, hright]
      ring

theorem IsDownwardCap.volumeReal_oneTurnSurvivor_ge_score_of_affine
    {U : Set Plane} (hU : IsDownwardCap U) {C h : ℝ} (hC : 0 < C)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hleft : capRoof U (-C) = 1 - h) (hright : capRoof U C = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hconvL : ConvexOn ℝ (Icc (-2 * C) (-C)) (sweptNiche U (Real.pi / 2)))
    (hconvR : ConvexOn ℝ (Icc C (2 * C)) (sweptNiche U (Real.pi / 2)))
    (hfit : ∀ x ∈ horizontalProjection U, sweptNiche U (Real.pi / 2) x ≤ capRoof U x) :
    capScore U (Real.pi / 2) + 2 * C - C * h -
      C * (sweptNiche U (Real.pi / 2) (-C) + sweptNiche U (Real.pi / 2) C) / 2 ≤
      volume.real (oneTurnSurvivor U) := by
  have harea := hU.volumeReal_oneTurnSurvivor_eq_centered_integrals hl hr hfit
  have hwing := hU.wing_niche_integrals_le hC hl hr hconvL hconvR
  rw [hU.middle_roof_integral_of_affine hC hleft hright haffine] at harea
  linarith

/-- The weaker CG inequality is now a statement about an actual full cap
maximizer and its actual endpoint heights. Only the remaining central
source-height inequality is exposed; the survivor and ordinary area
comparison are constructed in this proof. -/
theorem IsFullCapMaximizer.ordinary_area_necessary_of_middle_height_bound
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hleft : capRoof U (-C) = 1 - h) (hright : capRoof U C = 1)
    (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 37 / 50) (hh0 : 0 ≤ h) (hh1 : h ≤ 17 / 50)
    (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hmid : ∀ x ∈ Icc (-C) C, sweptNiche U (Real.pi / 2) x ≤
      (capRoof U (horizontalRight U) + capRoof U (horizontalLeft U)) / 2) :
    M / 2 + C * (3 - (capRoof U (horizontalRight U) +
      capRoof U (horizontalLeft U)) - 3 * h / 2) ≤ (22199 : ℝ) / 10000 := by
  have hC : 0 < C := by linarith
  have hminus : horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 = -C := by
    rw [hl, hr]; ring
  have hplus : horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 = C := by
    rw [hl, hr]; ring
  have haffine' : ∃ m c : ℝ, ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c := by
    simpa only [middleHalfInterval, hminus, hplus] using haffine
  have hfit := hU.sweptNiche_le_roof_of_middle_height_bound
    hl hr hleft hright hC0 hC1 hh0 hh1 hheight haffine hmid
  have hconv := hU.isCap.convexOn_sweptNiche_wings_of_roof_endpoints
    hl hr hleft hright hC0 hC1 hh1
  have harea := hU.isCap.volumeReal_oneTurnSurvivor_ge_score_of_affine
    hC hl hr hleft hright haffine' hconv.1 hconv.2 hfit
  have hordinary := hU.isCap.volumeReal_oneTurnSurvivor_le hfit
  have hsum := hU.endpoint_height_sum_of_affine hheight haffine
  rw [hminus, hplus, hleft, hright] at hsum
  have hsumC := congrArg (fun t : ℝ => C * t) hsum
  nlinarith [hU.reference_le]

end AmbidextrousSofa
