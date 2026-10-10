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
  unfold tiltedAffineCeiling
  fun_prop

theorem tilted_middle_affine_parameters {f : ℝ → ℝ} {a h m c : ℝ}
    (ha : 0 < a) (haffine : ∀ x ∈ Icc (-a / 2) (a / 2), f x = m * x + c)
    (hleft : f (-a / 2) = 1 - h) (hright : f (a / 2) = 1) :
    m = h / a ∧ c = 1 - h / 2 := by
  obtain ⟨hma, hmc⟩ := tilted_middle_slope ha haffine hleft hright
  exact ⟨(eq_div_iff ha.ne').mpr hma, by nlinarith only [hma, hmc]⟩

theorem IsDownwardCap.capRoof_le_tiltedAffineCeiling
    {U : Set Plane} (hU : IsDownwardCap U) {a h : ℝ} (ha : 0 < a)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c) :
    ∀ x ∈ horizontalProjection U, capRoof U x ≤ tiltedAffineCeiling a h x := by
  obtain ⟨m, c, hm⟩ := haffine
  obtain ⟨hmh, hch⟩ := tilted_middle_affine_parameters ha hm hleft hright
  have hproj : horizontalProjection U = Icc (-a) a := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
  have hA : -a / 2 ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith
  have hB : a / 2 ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith
  have hbound := hU.capRoof_le_affine_of_affine_segment hA hB (by linarith) hm
  intro x hx
  have hxbound := hbound x hx
  rw [hmh, hch] at hxbound
  unfold tiltedAffineCeiling
  linarith only [hxbound]

/-- The lower diagonal support has the sharper bound supplied by the
actual tilted affine ceiling, not by a raised auxiliary cap. -/
theorem IsDownwardCap.tilted_diagonalLeft_le
    {U : Set Plane} (hU : IsDownwardCap U) {a h : ℝ} (ha : 0 < a) (hha : h ≤ a)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c) :
    diagonalLeft U ≤ 1 + a - 3 * h / 2 := by
  have hz : h / a ≤ 1 := (div_le_one ha).mpr hha
  have hza : (h / a) * a = h := div_mul_cancel₀ h ha.ne'
  apply support_le_of_forall hU.nonempty
  intro p hp
  have hx : -a ≤ p.1 := by
    have h : p.1 ∈ horizontalProjection U := ⟨p, hp, rfl⟩
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl] at h
    exact h.1
  have hy := (le_capRoof hU.isCompact (show (p.1, p.2) ∈ U by simpa using hp)).trans
    (hU.capRoof_le_tiltedAffineCeiling ha hl hr hleft hright haffine p.1 ⟨p, hp, rfl⟩)
  have hprod := mul_nonneg (sub_nonneg.mpr hz) (show 0 ≤ p.1 + a by linarith only [hx])
  unfold tiltedAffineCeiling at hy
  simp only [coordDot, mul_neg_one, mul_one]
  nlinarith only [hy, hprod, hza]

theorem tilted_diagonal_intersection_mem {a h v : ℝ} (ha : 0 < a) (hha : h < a)
    (hv0 : a / 2 ≤ v) (hv1 : v ≤ a - h / 2) :
    (v - h / 2) / (1 - h / a) ∈ Icc (a / 2) a := by
  have hz : h / a < 1 := (div_lt_one ha).mpr hha
  have hd : 0 < 1 - h / a := sub_pos.mpr hz
  have hza : (h / a) * a = h := div_mul_cancel₀ h ha.ne'
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith only [hv0, hza]
  · apply (div_le_iff₀ hd).mpr
    nlinarith only [hv1, hza]

theorem integral_tiltedAffineCeiling_left {a : ℝ} (ha : 0 < a) (h : ℝ) :
    (∫ x in (-a)..(-a / 2), tiltedAffineCeiling a h x) = a / 2 - 5 * a * h / 8 := by
  unfold tiltedAffineCeiling
  rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
      ((show Continuous (fun x : ℝ => h / a * x) by fun_prop).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [smul_eq_mul]
  field_simp [ha.ne']
  ring

theorem integral_tilted_diagonal_left_roof {a h v : ℝ} (ha : 0 < a) (hha : h < a)
    (hv0 : a / 2 ≤ v) (hv1 : v ≤ a - h / 2) :
    (∫ x in (-a)..(-a / 2), min (tiltedAffineCeiling a h x) (1 - h + v + x)) =
      a / 2 - 5 * a * h / 8 - (a - v - h / 2) ^ 2 / (2 * (1 - h / a)) := by
  let d := 1 - h / a
  let q := (v - h / 2) / d
  have hd : 0 < d := sub_pos.mpr ((div_lt_one ha).mpr hha)
  have hza : (h / a) * a = h := div_mul_cancel₀ h ha.ne'
  have hq : q ∈ Icc (a / 2) a := tilted_diagonal_intersection_mem ha hha hv0 hv1
  have hqd : q * d = v - h / 2 := div_mul_cancel₀ _ hd.ne'
  have hfun (x : ℝ) : min (tiltedAffineCeiling a h x) (1 - h + v + x) =
      tiltedAffineCeiling a h x - d * max (-q - x) 0 := by
    rw [min_eq_left_sub_positive]
    have heq : tiltedAffineCeiling a h x - (1 - h + v + x) = d * (-q - x) := by
      dsimp [tiltedAffineCeiling, d] at hqd ⊢
      nlinarith only [hqd]
    rw [heq]
    congr 1
    simpa only [mul_zero] using (mul_max_of_nonneg (-q - x) 0 hd.le).symm
  have hramp : (∫ x in (-a)..(-a / 2), max (-q - x) 0) = (a - q) ^ 2 / 2 := by
    rw [integral_positive_ramp_sub,
      max_eq_left (by linarith only [hq.2] : 0 ≤ -q - -a),
      max_eq_right (by linarith only [hq.1] : -q - (-a / 2) ≤ 0)]
    ring
  have hwidth : a - q = (a - v - h / 2) / d := by
    apply (eq_div_iff hd.ne').mpr
    dsimp [d] at hqd ⊢
    nlinarith only [hqd, hza]
  simp_rw [hfun]
  rw [intervalIntegral.integral_sub ((continuous_tiltedAffineCeiling a h).intervalIntegrable _ _)
      ((show Continuous (fun x : ℝ => d * max (-q - x) 0) by fun_prop).intervalIntegrable _ _),
    integral_tiltedAffineCeiling_left ha, intervalIntegral.integral_const_mul, hramp, hwidth]
  change _ = a / 2 - 5 * a * h / 8 - (a - v - h / 2) ^ 2 / (2 * d)
  field_simp [hd.ne'] <;> ring

theorem tilted_diagonal_roof_loss {a h : ℝ} (ha : 0 < a) (hha : h < a) (v : ℝ) :
    (a - v - h / 2) ^ 2 / (2 * (1 - h / a)) - (a - v) ^ 2 / 2 + a * h / 8 =
      h * (v - a / 2) ^ 2 / (2 * (a - h)) := by
  rw [show 1 - h / a = (a - h) / a by field_simp [ha.ne']]
  field_simp [ha.ne', (sub_pos.mpr hha).ne']
  ring

/-- The literal left charged roof, integrated under its two actual
supporting lines. -/
theorem IsDownwardCap.integral_capRoof_left_le_tilted_diagonal
    {U : Set Plane} (hU : IsDownwardCap U) {a h v : ℝ} (ha : 0 < a) (hha : h < a)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hv : diagonalLeft U = 1 - h + v) (hv0 : a / 2 ≤ v) :
    (∫ x in (-a)..(-a / 2), capRoof U x) ≤
      a / 2 - 5 * a * h / 8 - (a - v - h / 2) ^ 2 / (2 * (1 - h / a)) := by
  have hv1 : v ≤ a - h / 2 := by
    have h := hU.tilted_diagonalLeft_le ha hha.le hl hr hleft hright haffine
    rw [hv] at h
    linarith only [h]
  rw [← integral_tilted_diagonal_left_roof ha hha hv0 hv1]
  apply intervalIntegral.integral_mono_on (by linarith : -a ≤ -a / 2)
    (hU.intervalIntegrable_capRoof _ _)
    (((continuous_tiltedAffineCeiling a h).min (by fun_prop)).intervalIntegrable _ _)
  intro x hx
  have hxU : x ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
    exact ⟨hx.1, by linarith only [hx.2, ha]⟩
  apply le_min (hU.capRoof_le_tiltedAffineCeiling ha hl hr hleft hright haffine x hxU)
  have h := hU.capRoof_le_diagonalLeft hxU
  rwa [hv] at h

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
  have hL := hU.integral_capRoof_left_le_tilted_diagonal ha hha hl hr hleft hright haffine hv hvv.1
  have hR : (∫ x in (a / 2)..a, capRoof U x) ≤ a / 2 - (a - u) ^ 2 / 2 := by
    rw [← integral_diagonal_right_roof huv.1 huv.2]
    apply intervalIntegral.integral_mono_on (by linarith : a / 2 ≤ a)
      (hU.intervalIntegrable_capRoof _ _)
      ((show Continuous (fun x : ℝ => min 1 (1 + u - x)) by fun_prop).intervalIntegrable _ _)
    intro x hx
    apply le_min (capRoof_le_one hU.isCompact hU.inStrip x)
    have hxU : x ∈ horizontalProjection U := by
      rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
      exact ⟨by linarith only [hx.1, ha], hx.2⟩
    have h := hU.capRoof_le_diagonalRight hxU
    rwa [hu] at h
  have hD := hU.diagonalRoofDeficit_eq h huv hvv
  have hLoss := tilted_diagonal_roof_loss ha hha v
  linarith only [hL, hR, hD, hLoss]

end AmbidextrousSofa
