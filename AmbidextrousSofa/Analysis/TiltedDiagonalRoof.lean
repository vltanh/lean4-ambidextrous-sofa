module

public import AmbidextrousSofa.Analysis.FullWidthGap
public import AmbidextrousSofa.Analysis.FacetPinning

@[expose] public section

/-!
# The actual affine ceiling and its mandatory exterior deficit

The lower middle endpoint and higher endpoint determine a global affine
ceiling of the actual concave roof. Its intersection with the lower
diagonal support removes a literal charged triangle. Integrating this
majorant gives both the perspective roof formula and the mandatory tilt
loss relative to the earlier diagonal relaxation.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def tiltedAffineCeiling (a h x : ℝ) : ℝ := 1 - h / 2 + (h / a) * x

theorem continuous_tiltedAffineCeiling (a h : ℝ) : Continuous (tiltedAffineCeiling a h) := by
  unfold tiltedAffineCeiling; fun_prop

theorem IsDownwardCap.capRoof_le_tiltedAffineCeiling
    {U : Set Plane} (hU : IsDownwardCap U) {a h : ℝ} (ha : 0 < a)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c) :
    ∀ x ∈ horizontalProjection U, capRoof U x ≤ tiltedAffineCeiling a h x := by
  obtain ⟨m, c, hm⟩ := haffine
  obtain ⟨hma, hmc⟩ := tilted_middle_slope ha hm hleft hright
  obtain rfl : m = h / a := (eq_div_iff ha.ne').2 hma
  have hproj : horizontalProjection U = Icc (-a) a := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
  intro x hx
  have := hU.capRoof_le_affine_of_affine_segment (a := -a / 2) (b := a / 2)
    (hproj ▸ ⟨by linarith, by linarith⟩) (hproj ▸ ⟨by linarith, by linarith⟩) (by linarith) hm x hx
  unfold tiltedAffineCeiling
  linarith

/-- The lower diagonal support has the sharper bound supplied by the
actual tilted affine ceiling, not by a raised auxiliary cap. -/
theorem IsDownwardCap.tilted_diagonalLeft_le
    {U : Set Plane} (hU : IsDownwardCap U) {a h : ℝ} (ha : 0 < a) (hha : h ≤ a)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c) :
    diagonalLeft U ≤ 1 + a - 3 * h / 2 := by
  refine support_le_of_forall hU.nonempty fun p hp => ?_
  have hx : horizontalLeft U ≤ p.1 :=
    csInf_le (isCompact_horizontalProjection hU.isCompact).bddBelow ⟨p, hp, rfl⟩
  have hy := (le_capRoof hU.isCompact hp).trans
    (hU.capRoof_le_tiltedAffineCeiling ha hl hr hleft hright haffine p.1 ⟨p, hp, rfl⟩)
  simp only [coordDot, tiltedAffineCeiling] at hy ⊢
  linarith [mul_nonneg (sub_nonneg.2 ((div_le_one ha).2 hha)) (show 0 ≤ p.1 + a by linarith),
    div_mul_cancel₀ h ha.ne']

theorem tilted_diagonal_intersection_mem {a h v : ℝ} (ha : 0 < a) (hha : h < a)
    (hv0 : a / 2 ≤ v) (hv1 : v ≤ a - h / 2) :
    (v - h / 2) / (1 - h / a) ∈ Icc (a / 2) a := by
  have hza : h / a * a = h := div_mul_cancel₀ h ha.ne'
  rw [mem_Icc, le_div_iff₀ (sub_pos.2 ((div_lt_one ha).2 hha)),
    div_le_iff₀ (sub_pos.2 ((div_lt_one ha).2 hha))]
  constructor <;> linarith

theorem integral_tiltedAffineCeiling_left {a : ℝ} (ha : 0 < a) (h : ℝ) :
    (∫ x in (-a)..(-a / 2), tiltedAffineCeiling a h x) = a / 2 - 5 * a * h / 8 := by
  unfold tiltedAffineCeiling
  rw [intervalIntegral.integral_add intervalIntegrable_const
      ((show Continuous (fun x : ℝ => h / a * x) by fun_prop).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id, smul_eq_mul]
  field_simp
  ring

theorem integral_tilted_diagonal_left_roof {a h v : ℝ} (ha : 0 < a) (hha : h < a)
    (hv0 : a / 2 ≤ v) (hv1 : v ≤ a - h / 2) :
    (∫ x in (-a)..(-a / 2), min (tiltedAffineCeiling a h x) (1 - h + v + x)) =
      a / 2 - 5 * a * h / 8 - (a - v - h / 2) ^ 2 / (2 * (1 - h / a)) := by
  have hd : 0 < 1 - h / a := sub_pos.2 ((div_lt_one ha).2 hha)
  obtain ⟨hq0, hq1⟩ := tilted_diagonal_intersection_mem ha hha hv0 hv1
  set d := 1 - h / a
  set q := (v - h / 2) / d
  have hqd : q * d = v - h / 2 := div_mul_cancel₀ _ hd.ne'
  have hza : h / a * a = h := div_mul_cancel₀ h ha.ne'
  have hfun (x : ℝ) : min (tiltedAffineCeiling a h x) (1 - h + v + x) =
      tiltedAffineCeiling a h x - d * max (-q - x) 0 := by
    rw [min_eq_left_sub_positive, mul_max_of_nonneg _ _ hd.le, mul_zero]
    congr 2
    dsimp only [tiltedAffineCeiling, d] at hqd ⊢
    linarith
  have hwidth : -q - -a = (a - v - h / 2) / d := by
    rw [eq_div_iff hd.ne']
    dsimp only [d] at hqd ⊢
    linarith
  simp_rw [hfun]
  rw [intervalIntegral.integral_sub ((continuous_tiltedAffineCeiling a h).intervalIntegrable _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _), integral_tiltedAffineCeiling_left ha,
    intervalIntegral.integral_const_mul, integral_positive_ramp_sub,
    max_eq_left (by linarith : 0 ≤ -q - -a), max_eq_right (by linarith : -q - (-a / 2) ≤ 0), hwidth]
  field_simp
  ring

theorem tilted_diagonal_roof_loss {a h : ℝ} (ha : 0 < a) (hha : h < a) (v : ℝ) :
    (a - v - h / 2) ^ 2 / (2 * (1 - h / a)) - (a - v) ^ 2 / 2 + a * h / 8 =
      h * (v - a / 2) ^ 2 / (2 * (a - h)) := by
  rw [show 1 - h / a = (a - h) / a by field_simp]
  field_simp [(sub_pos.mpr hha).ne']
  ring

/-- A nonzero tilt forces this ordinary exterior area deficit, before
any additional nearby-angle cut is made. -/
theorem IsDownwardCap.diagonalRoofDeficit_ge_tilt_loss
    {U : Set Plane} (hU : IsDownwardCap U) {a h u v : ℝ} (ha : 0 < a) (hha : h < a)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hu : diagonalRight U = 1 + u) (hv : diagonalLeft U = 1 - h + v)
    (huv : u ∈ Icc (a / 2) a) (hvv : v ∈ Icc (a / 2) a) :
    h * (v - a / 2) ^ 2 / (2 * (a - h)) ≤ diagonalRoofDeficit U a h u v := by
  have hproj : horizontalProjection U = Icc (-a) a := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
  have hL : (∫ x in (-a)..(-a / 2), capRoof U x) ≤
      a / 2 - 5 * a * h / 8 - (a - v - h / 2) ^ 2 / (2 * (1 - h / a)) := by
    rw [← integral_tilted_diagonal_left_roof ha hha hvv.1
      (by linarith [hU.tilted_diagonalLeft_le ha hha.le hl hr hleft hright haffine])]
    refine intervalIntegral.integral_mono_on (by linarith) (hU.intervalIntegrable_capRoof _ _)
      (((continuous_tiltedAffineCeiling a h).min (by fun_prop)).intervalIntegrable _ _)
      fun x hx => ?_
    have hxU : x ∈ horizontalProjection U := hproj ▸ ⟨hx.1, by linarith [hx.2]⟩
    exact le_min (hU.capRoof_le_tiltedAffineCeiling ha hl hr hleft hright haffine x hxU)
      (by linarith [hU.capRoof_le_diagonalLeft hxU])
  have hR : (∫ x in (a / 2)..a, capRoof U x) ≤ a / 2 - (a - u) ^ 2 / 2 := by
    rw [← integral_diagonal_right_roof huv.1 huv.2]
    refine intervalIntegral.integral_mono_on (by linarith) (hU.intervalIntegrable_capRoof _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _) fun x hx => ?_
    have hxU : x ∈ horizontalProjection U := hproj ▸ ⟨by linarith [hx.1], hx.2⟩
    exact le_min (capRoof_le_one hU.isCompact hU.inStrip x)
      (by linarith [hU.capRoof_le_diagonalRight hxU])
  linarith [hU.diagonalRoofDeficit_eq h huv hvv, tilted_diagonal_roof_loss ha hha v]

end AmbidextrousSofa
