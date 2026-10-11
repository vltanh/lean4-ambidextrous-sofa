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

theorem IsDownwardCap.volumeReal_oneTurnSurvivor_eq_intervalIntegral {U : Set Plane}
    (hU : IsDownwardCap U)
    (hfit : ∀ x ∈ horizontalProjection U, sweptNiche U (Real.pi / 2) x ≤ capRoof U x) :
    volume.real (oneTurnSurvivor U) = ∫ x in horizontalLeft U..horizontalRight U,
      capRoof U x - sweptNiche U (Real.pi / 2) x := by
  have hproj := hU.horizontalProjection_eq_Icc
  have hnonneg : ∀ᵐ x ∂volume.restrict (Icc (horizontalLeft U) (horizontalRight U)),
      0 ≤ capRoof U x - sweptNiche U (Real.pi / 2) x := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact sub_nonneg.mpr (hfit x (hproj ▸ hx))
  rw [Measure.real, hU.oneTurnSurvivor_eq_verticalIntervalRegion, hproj,
    volume_verticalIntervalRegion_eq_lintegral measurableSet_Icc
      hU.continuous_sweptNiche_pi_div_two.measurable hU.measurable_capRoof,
    ← ofReal_integral_eq_lintegral_ofReal (f := fun x => capRoof U x - sweptNiche U (Real.pi / 2) x)
      ((hU.integrableOn_capRoof_Icc _ _).sub hU.continuous_sweptNiche_pi_div_two.integrableOn_Icc)
      hnonneg,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hnonneg), integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact)]

theorem IsDownwardCap.volumeReal_oneTurnSurvivor_eq_centered_integrals
    {U : Set Plane} (hU : IsDownwardCap U) {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hfit : ∀ x ∈ horizontalProjection U, sweptNiche U (Real.pi / 2) x ≤ capRoof U x) :
    volume.real (oneTurnSurvivor U) = capScore U (Real.pi / 2) +
      (∫ x in (-C)..C, capRoof U x) -
      ((∫ x in (-2 * C)..(-C), sweptNiche U (Real.pi / 2) x) +
        ∫ x in C..(2 * C), sweptNiche U (Real.pi / 2) x) := by
  have hscore := hU.capScore_eq_intervalSpatialScore (Real.pi / 2)
  rw [hl, hr, intervalSpatialScore, show -2 * C + (2 * C - -2 * C) / 4 = -C by ring,
    show 2 * C - (2 * C - -2 * C) / 4 = C by ring] at hscore
  simp_rw [hU.partialBarrier_pi_div_two] at hscore
  have hroof := hU.intervalIntegrable_capRoof
  have hniche := hU.continuous_sweptNiche_pi_div_two.intervalIntegrable (μ := volume)
  have := intervalIntegral.integral_add_adjacent_intervals (hroof (-2 * C) (-C)) (hroof (-C) C)
  have := intervalIntegral.integral_add_adjacent_intervals (hroof (-2 * C) C) (hroof C (2 * C))
  have := intervalIntegral.integral_add_adjacent_intervals (hniche (-2 * C) (-C)) (hniche (-C) C)
  have := intervalIntegral.integral_add_adjacent_intervals (hniche (-2 * C) C) (hniche C (2 * C))
  rw [hU.volumeReal_oneTurnSurvivor_eq_intervalIntegral hfit, hl, hr,
    intervalIntegral.integral_sub (hroof _ _) (hniche _ _)]
  linarith

theorem integral_roofChord (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) :
    (∫ x in a..b, roofChord f a b x) = (b - a) * (f a + f b) / 2 := by
  unfold roofChord
  rw [intervalIntegral.integral_add intervalIntegrable_const ((by fun_prop :
      Continuous fun x : ℝ => (f b - f a) / (b - a) * (x - a)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right (fun x => x),
    integral_id]
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_self]
  field_simp [(sub_pos.mpr hab).ne']
  ring

theorem ConvexOn.integral_le_trapezoid {f : ℝ → ℝ} {a b : ℝ}
    (hf : ConvexOn ℝ (Icc a b) f) (hab : a < b)
    (hfi : IntervalIntegrable f volume a b) :
    (∫ x in a..b, f x) ≤ (b - a) * (f a + f b) / 2 := by
  rw [← integral_roofChord f hab]
  refine intervalIntegral.integral_mono_on hab.le hfi
    ((continuous_roofChord f a b).intervalIntegrable a b) fun x hx => ?_
  -- A convex function lies below its chord.
  have hba : 0 < b - a := sub_pos.mpr hab
  have h := hf.2 ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ (div_nonneg (sub_nonneg.mpr hx.2) hba.le)
    (div_nonneg (sub_nonneg.mpr hx.1) hba.le) (by field_simp; ring)
  rw [roofChord_eq_interpolation f hab]
  simpa only [smul_eq_mul, show (b - x) / (b - a) * a + (x - a) / (b - a) * b = x by
    field_simp; ring] using h

theorem middle_roof_integral_of_affine
    {U : Set Plane} {C h : ℝ} (hC : 0 < C)
    (hleft : capRoof U (-C) = 1 - h) (hright : capRoof U C = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c) :
    (∫ x in (-C)..C, capRoof U x) = 2 * C - C * h := by
  obtain ⟨m, c, haffine⟩ := haffine
  have hCC : -C < C := by linarith
  rw [intervalIntegral.integral_congr (g := roofChord (capRoof U) (-C) C) fun x hx =>
    eqOn_roofChord_of_affine hCC haffine (uIcc_of_le hCC.le ▸ hx), integral_roofChord _ hCC,
    hleft, hright]
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
  -- The convex wing niches lie below their chords and vanish at the outer endpoints.
  have hL := ConvexOn.integral_le_trapezoid hconvL (by linarith)
    (hU.continuous_sweptNiche_pi_div_two.intervalIntegrable _ _)
  have hR := ConvexOn.integral_le_trapezoid hconvR (by linarith)
    (hU.continuous_sweptNiche_pi_div_two.intervalIntegrable _ _)
  rw [show sweptNiche U (Real.pi / 2) (-2 * C) = 0 from
    hl ▸ hU.sweptNiche_eq_zero_of_le_left le_rfl] at hL
  rw [show sweptNiche U (Real.pi / 2) (2 * C) = 0 from
    hr ▸ hU.sweptNiche_eq_zero_of_right_le le_rfl] at hR
  linarith [hU.volumeReal_oneTurnSurvivor_eq_centered_integrals hl hr hfit,
    middle_roof_integral_of_affine hC hleft hright haffine]

end AmbidextrousSofa
