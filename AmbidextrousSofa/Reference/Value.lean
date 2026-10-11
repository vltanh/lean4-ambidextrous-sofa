module

public import AmbidextrousSofa.Reference.Stationarity
public import AmbidextrousSofa.Reference.Body
public import AmbidextrousSofa.Measure.SignedRoofIntegral
public import AmbidextrousSofa.Measure.SymmetricBody

@[expose] public section

/-!
# Exact value and actual area of the reference

The Euler identity against the reference itself evaluates the quadratic
part by its actual endpoint fluxes. The remaining three phase integrals
have elementary antiderivatives. The cubic root identity then converts the
result to `M`; no area or optimality statement is an input to this calculation.
The actual support-area and signed-roof formulas then identify that value with
the concrete cap score and with the area of the symmetric trimmed hull.
-/

noncomputable section

open Set MeasureTheory
open AmbidextrousSofa.Analysis

namespace AmbidextrousSofa.Reference

theorem referenceFD_zero : referenceFD 0 = 1 / 2 := by
  simp only [referenceFD, if_pos beta_pos.le, fEarlyD_zero]

theorem referenceGD_zero : referenceGD 0 = 2 * A - 1 := by
  simp only [referenceGD, if_pos beta_pos.le, gEarlyD_zero]

theorem referenceFD_pi_div_two : referenceFD (Real.pi / 2) = 2 / 3 * A - 1 := by
  simp only [referenceFD, if_neg (not_le.mpr beta_lt_pi_div_two),
    if_neg (not_le.mpr lateSwitch_lt_pi_div_two), fLateD_pi_div_two]

theorem referenceGD_pi_div_two : referenceGD (Real.pi / 2) = -1 / 2 := by
  simp only [referenceGD, if_neg (not_le.mpr beta_lt_pi_div_two),
    if_neg (not_le.mpr lateSwitch_lt_pi_div_two), gLateD_pi_div_two]
  ring

theorem referenceF_beta : referenceF beta = cosBeta + 1 / 2 * sinBeta := by
  simp only [referenceF, if_pos le_rfl, fEarly, sinBeta, cosBeta]

theorem referenceG_beta : referenceG beta =
    (2 * A - 1) * sinBeta + 1 / 2 * cosBeta + 1 / 2 := by
  simp only [referenceG, if_pos le_rfl, gEarly, sinBeta, cosBeta]

theorem referenceF_lateSwitch : referenceF lateSwitch =
    (1 - 2 / 3 * A) * sinBeta + 1 / 2 * cosBeta + 1 / 2 := by
  rw [referenceF, if_neg (not_le.mpr beta_lt_lateSwitch), if_pos le_rfl, f_matching_last]
  simp only [fLate, lateSwitch, Real.cos_pi_div_two_sub,
    Real.sin_pi_div_two_sub, sinBeta, cosBeta]

theorem referenceG_lateSwitch : referenceG lateSwitch =
    (8 / 3 * A - 1) * cosBeta + 1 / 2 * sinBeta := by
  rw [referenceG, if_neg (not_le.mpr beta_lt_lateSwitch), if_pos le_rfl, g_matching_last]
  simp only [gLate, lateSwitch, Real.cos_pi_div_two_sub,
    Real.sin_pi_div_two_sub, sinBeta, cosBeta]

/-- Subtracting the self-variation leaves only the linear and constant
parts of the active phase quadratic. The formula is valid at the contacts. -/
theorem twice_density_sub_self_variation (u : QuarterPair) (t : ℝ) :
    2 * adaptiveDensity u t - adaptiveLinearDensity u u t =
      2 - u.f t - u.g t + (u.fD t - u.gD t) / 2 - min (u.p t) 0 + max (u.q t) 0 := by
  rcases le_total (u.p t) 0 with hp | hp <;> rcases le_total (u.q t) 0 with hq | hq
  all_goals
    simp only [adaptiveDensity, adaptiveLinearDensity, min_eq_left hp,
      min_eq_right hp, max_eq_left hq, max_eq_right hq]
    try unfold QuarterPair.p
    try unfold QuarterPair.q
    ring

def referenceValueRemainder (t : ℝ) : ℝ :=
  2 * adaptiveDensity referencePair t - adaptiveLinearDensity referencePair referencePair t

theorem continuousOn_referenceValueRemainder :
    ContinuousOn referenceValueRemainder (Icc (0 : ℝ) (Real.pi / 2)) :=
  ((continuousOn_adaptiveDensity referencePair).const_mul 2).sub
    (continuousOn_adaptiveLinearDensity referencePair referencePair)

theorem referenceValueRemainder_early {t : ℝ} (ht : t ∈ Icc (0 : ℝ) beta) :
    referenceValueRemainder t =
      1 / 2 - (2 * A - 1 / 4) * Real.sin t + (A - 3 / 4) * Real.cos t := by
  rw [referenceValueRemainder, twice_density_sub_self_variation]
  change 2 - referenceF t - referenceG t + (referenceFD t - referenceGD t) / 2 -
    min (momentP t) 0 + max (momentQ t) 0 = _
  rw [min_eq_right (momentP_nonneg_early ht),
    max_eq_left (momentQ_nonneg_before_lateSwitch ⟨ht.1, ht.2.trans beta_lt_lateSwitch.le⟩)]
  unfold momentQ
  simp only [referenceF, referenceG, referenceFD, referenceGD, if_pos ht.2,
    fEarly, gEarly, fEarlyD, gEarlyD]
  ring

theorem referenceValueRemainder_middle {t : ℝ} (ht : t ∈ Icc beta lateSwitch) :
    referenceValueRemainder t = (referenceGD t - referenceFD t) / 2 := by
  rw [referenceValueRemainder, twice_density_sub_self_variation]
  change 2 - referenceF t - referenceG t + (referenceFD t - referenceGD t) / 2 -
    min (momentP t) 0 + max (momentQ t) 0 = _
  rw [min_eq_left (momentP_nonpos_after_beta ⟨ht.1, ht.2.trans lateSwitch_lt_pi_div_two.le⟩),
    max_eq_left (momentQ_nonneg_before_lateSwitch ⟨beta_pos.le.trans ht.1, ht.2⟩)]
  unfold momentP momentQ
  ring

theorem referenceValueRemainder_late {t : ℝ}
    (ht : t ∈ Ioo lateSwitch (Real.pi / 2)) :
    referenceValueRemainder t =
      1 / 2 + (1 / 4 - A / 3) * Real.sin t - (3 / 4 + 2 / 3 * A) * Real.cos t := by
  rw [referenceValueRemainder, twice_density_sub_self_variation]
  change 2 - referenceF t - referenceG t + (referenceFD t - referenceGD t) / 2 -
    min (momentP t) 0 + max (momentQ t) 0 = _
  rw [min_eq_left (momentP_nonpos_after_beta ⟨beta_lt_lateSwitch.le.trans ht.1.le, ht.2.le⟩),
    max_eq_right (momentQ_nonpos_late ⟨ht.1.le, ht.2.le⟩)]
  unfold momentP
  simp only [referenceF, referenceG, referenceFD, referenceGD,
    if_neg (not_le.mpr (beta_lt_lateSwitch.trans ht.1)), if_neg (not_le.mpr ht.1),
    fLate, gLate, fLateD, gLateD]
  ring

def earlyValuePrimitive (t : ℝ) : ℝ :=
  t / 2 + (2 * A - 1 / 4) * Real.cos t + (A - 3 / 4) * Real.sin t

def lateValuePrimitive (t : ℝ) : ℝ :=
  t / 2 - (1 / 4 - A / 3) * Real.cos t - (3 / 4 + 2 / 3 * A) * Real.sin t

theorem hasDerivAt_earlyValuePrimitive (t : ℝ) :
    HasDerivAt earlyValuePrimitive
      (1 / 2 - (2 * A - 1 / 4) * Real.sin t + (A - 3 / 4) * Real.cos t) t := by
  apply ((((hasDerivAt_id t).div_const 2).add
    ((Real.hasDerivAt_cos t).const_mul (2 * A - 1 / 4))).add
      ((Real.hasDerivAt_sin t).const_mul (A - 3 / 4))).congr_deriv
  ring

theorem hasDerivAt_lateValuePrimitive (t : ℝ) :
    HasDerivAt lateValuePrimitive
      (1 / 2 + (1 / 4 - A / 3) * Real.sin t - (3 / 4 + 2 / 3 * A) * Real.cos t) t := by
  apply ((((hasDerivAt_id t).div_const 2).sub
    ((Real.hasDerivAt_cos t).const_mul (1 / 4 - A / 3))).sub
      ((Real.hasDerivAt_sin t).const_mul (3 / 4 + 2 / 3 * A))).congr_deriv
  ring

theorem integral_referenceValueRemainder_early :
    (∫ t in (0 : ℝ)..beta, referenceValueRemainder t) =
      earlyValuePrimitive beta - earlyValuePrimitive 0 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le beta_pos.le
    (by unfold earlyValuePrimitive; fun_prop)
  · intro t ht
    rw [referenceValueRemainder_early ⟨ht.1.le, ht.2.le⟩]
    exact hasDerivAt_earlyValuePrimitive t
  · exact ContinuousOn.intervalIntegrable_of_Icc beta_pos.le
      (continuousOn_referenceValueRemainder.mono (fun _ ht =>
        ⟨ht.1, ht.2.trans beta_lt_pi_div_two.le⟩))

theorem integral_referenceValueRemainder_middle :
    (∫ t in beta..lateSwitch, referenceValueRemainder t) =
      (referenceG lateSwitch - referenceF lateSwitch) / 2 -
        (referenceG beta - referenceF beta) / 2 := by
  have hcont : Continuous (fun t => (referenceG t - referenceF t) / 2) :=
    (continuous_referenceG.sub continuous_referenceF).div_const 2
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le beta_lt_lateSwitch.le hcont.continuousOn
  · intro t ht
    rw [referenceValueRemainder_middle ⟨ht.1.le, ht.2.le⟩]
    exact ((hasDerivAt_referenceG t).sub (hasDerivAt_referenceF t)).div_const 2
  · exact ContinuousOn.intervalIntegrable_of_Icc beta_lt_lateSwitch.le
      (continuousOn_referenceValueRemainder.mono (fun _ ht =>
        ⟨beta_pos.le.trans ht.1, ht.2.trans lateSwitch_lt_pi_div_two.le⟩))

theorem integral_referenceValueRemainder_late :
    (∫ t in lateSwitch..(Real.pi / 2), referenceValueRemainder t) =
      lateValuePrimitive (Real.pi / 2) - lateValuePrimitive lateSwitch := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le lateSwitch_lt_pi_div_two.le
    (by unfold lateValuePrimitive; fun_prop)
  · intro t ht
    rw [referenceValueRemainder_late ht]
    exact hasDerivAt_lateValuePrimitive t
  · exact ContinuousOn.intervalIntegrable_of_Icc lateSwitch_lt_pi_div_two.le
      (continuousOn_referenceValueRemainder.mono (fun _ ht =>
        ⟨lateSwitch_pos.le.trans ht.1, ht.2⟩))

theorem integral_referenceValueRemainder :
    (∫ t in (0 : ℝ)..(Real.pi / 2), referenceValueRemainder t) =
      4 * A * cosBeta - 8 / 3 * A - 1 + beta := by
  have hE := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) beta_pos.le
    (continuousOn_referenceValueRemainder.mono (fun _ ht =>
      ⟨ht.1, ht.2.trans beta_lt_pi_div_two.le⟩))
  have hM := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) beta_lt_lateSwitch.le
    (continuousOn_referenceValueRemainder.mono (fun _ ht =>
      ⟨beta_pos.le.trans ht.1, ht.2.trans lateSwitch_lt_pi_div_two.le⟩))
  have hL := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) lateSwitch_lt_pi_div_two.le
    (continuousOn_referenceValueRemainder.mono (fun _ ht =>
      ⟨lateSwitch_pos.le.trans ht.1, ht.2⟩))
  rw [← intervalIntegral.integral_add_adjacent_intervals (hE.trans hM) hL,
    ← intervalIntegral.integral_add_adjacent_intervals hE hM,
    integral_referenceValueRemainder_early, integral_referenceValueRemainder_middle,
    integral_referenceValueRemainder_late, referenceF_beta, referenceG_beta,
    referenceF_lateSwitch, referenceG_lateSwitch]
  simp only [earlyValuePrimitive, lateValuePrimitive, lateSwitch, Real.sin_zero,
    Real.cos_zero, Real.sin_pi_div_two, Real.cos_pi_div_two,
    Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, sinBeta, cosBeta]
  ring

/-- The actual self-variation is evaluated by the four endpoint fluxes. -/
theorem reference_self_variation :
    adaptiveFirstVariation referencePair referencePair = 16 / 3 * A - 1 := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have htop : Real.pi / 2 ∈ Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], le_rfl⟩
  rw [adaptiveFirstVariation_eq_boundary referencePair referencePair
    (fun _ ht => referencePair_eulerF ht) (fun _ ht => referencePair_eulerG ht),
    referencePair_fluxF_eq htop, referencePair_fluxG_eq htop,
    referencePair_fluxF_eq hzero, referencePair_fluxG_eq hzero]
  simp only [referencePair, referenceF_zero, referenceG_zero, referenceF_pi_div_two,
    referenceG_pi_div_two, adjustedMomentP, adjustedMomentQ, if_pos beta_pos.le,
    if_neg (not_le.mpr beta_lt_pi_div_two), if_neg (not_le.mpr lateSwitch_lt_pi_div_two),
    Real.sin_zero, Real.cos_zero, Real.sin_pi_div_two, Real.cos_pi_div_two]
  ring

theorem adaptiveFunctional_reference_exact :
    adaptiveFunctional referencePair = 4 / 3 * A + 2 * A * cosBeta - 1 + beta / 2 := by
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hd := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hL
    (continuousOn_adaptiveDensity referencePair)
  have hv := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hL
    (continuousOn_adaptiveLinearDensity referencePair referencePair)
  have h := integral_referenceValueRemainder
  unfold referenceValueRemainder at h
  rw [intervalIntegral.integral_sub (hd.const_mul 2) hv,
    intervalIntegral.integral_const_mul, ← adaptiveFunctional, ← adaptiveFirstVariation,
    reference_self_variation] at h
  linarith

theorem four_A_cosBeta_eq_reciprocal : 4 * A * cosBeta = 1 / Y := by
  calc
    4 * A * cosBeta = 4 * (A * cosBeta) := by ring
    _ = 4 * (1 / (4 * Y)) := by rw [A_mul_cosBeta]
    _ = 1 / Y := by field_simp [Y_ne_zero] <;> ring

/-- The width term is still present in the support functional. -/
theorem adaptiveFunctional_reference_eq_M_add_width :
    adaptiveFunctional referencePair = (M + 8 / 3 * A) / 2 := by
  have hM : M - beta + 2 = 1 / Y :=
    (eq_div_iff Y_ne_zero).mpr M_sub_beta_add_two_mul_Y
  rw [adaptiveFunctional_reference_exact]
  nlinarith [four_A_cosBeta_eq_reciprocal]

theorem twice_adaptiveFunctional_reference_sub_width :
    2 * adaptiveFunctional referencePair - 8 / 3 * A = M := by
  rw [adaptiveFunctional_reference_eq_M_add_width]
  ring

/-- A finite measurable phase switch preserves interval integrability. This
allows the actual right second derivatives to jump at both contacts. -/
theorem intervalIntegrable_if_lt {a b c : ℝ} {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable (fun t => if t < c then f t else g t) volume a b := by
  rw [intervalIntegrable_iff] at hf hg ⊢
  exact Integrable.piecewise (s := Iio c) measurableSet_Iio hf.integrableOn hg.integrableOn

theorem intervalIntegrable_referenceFSecond (a b : ℝ) :
    IntervalIntegrable referenceFSecond volume a b := by
  have hE : Continuous (fun t : ℝ => -Real.cos t - 1 / 2 * Real.sin t) := by fun_prop
  have hM : Continuous (fun t : ℝ =>
      -(R / 4) * Real.cos (t / 2 + Real.pi / 8) - k * Real.cos t -
        1 / 2 * Real.sin t) := by fun_prop
  have hL : Continuous (fun t : ℝ =>
      -(1 - 2 / 3 * A) * Real.cos t - 1 / 2 * Real.sin t) := by fun_prop
  exact intervalIntegrable_if_lt (hE.intervalIntegrable a b)
    (intervalIntegrable_if_lt (hM.intervalIntegrable a b) (hL.intervalIntegrable a b))

theorem intervalIntegrable_referenceGSecond (a b : ℝ) :
    IntervalIntegrable referenceGSecond volume a b := by
  have hE : Continuous (fun t : ℝ =>
      -(2 * A - 1) * Real.sin t - 1 / 2 * Real.cos t) := by fun_prop
  have hM : Continuous (fun t : ℝ =>
      -(R / 4) * Real.sin (t / 2 + Real.pi / 8) + k * Real.sin t -
        1 / 2 * Real.cos t) := by fun_prop
  have hL : Continuous (fun t : ℝ =>
      -(8 / 3 * A - 1) * Real.sin t - 1 / 2 * Real.cos t) := by fun_prop
  exact intervalIntegrable_if_lt (hE.intervalIntegrable a b)
    (intervalIntegrable_if_lt (hM.intervalIntegrable a b) (hL.intervalIntegrable a b))

theorem neg_referenceGD_zero : -referenceGD 0 = topLeft := by
  rw [referenceGD_zero]
  unfold topLeft
  ring

theorem neg_referenceFD_pi_div_two : -referenceFD (Real.pi / 2) = topRight := by
  rw [referenceFD_pi_div_two]
  unfold topRight
  ring

/-- The support integral is obtained from actual roof points on both arcs
and the realized top face. No prescribed area is an input. -/
theorem volumeReal_referenceCap_eq_support_integral :
    volume.real referenceCap = 1 / 2 * ∫ t in (0 : ℝ)..(Real.pi / 2),
      (referenceF t ^ 2 - referenceFD t ^ 2) +
        (referenceG t ^ 2 - referenceGD t ^ 2) := by
  apply isDownwardCap_referenceCap.volumeReal_eq_support_energy
    continuous_referenceF continuous_referenceG continuous_referenceFD continuous_referenceGD
    (fun t _ => (hasDerivAt_referenceF t).hasDerivWithinAt)
    (fun t _ => (hasDerivAt_referenceG t).hasDerivWithinAt)
    (fun t _ => hasDerivWithinAt_referenceFD_right t)
    (fun t _ => hasDerivWithinAt_referenceGD_right t)
    (intervalIntegrable_referenceFSecond 0 (Real.pi / 2))
    (intervalIntegrable_referenceGSecond 0 (Real.pi / 2))
    (fun t ht => referenceHull_subset_referenceCap (fBoundary_mem_referenceHull ht))
    (fun t ht => referenceHull_subset_referenceCap (gBoundary_mem_referenceHull ht))
    (fun t ht => angleSupport_referenceCap_eq_f ⟨ht.1.le, ht.2.le⟩)
    (fun t ht => angleSupport_referenceCap_eq_g ⟨ht.1.le, ht.2.le⟩)
  · rw [horizontalLeft_referenceCap, referenceG_pi_div_two]
    ring
  · rw [horizontalRight_referenceCap, referenceF_zero]
  · exact referenceF_pi_div_two
  · exact referenceG_zero
  · rw [neg_referenceGD_zero, neg_referenceFD_pi_div_two]
    exact topLeft_lt_topRight.le
  · intro x hx
    rw [neg_referenceGD_zero, neg_referenceFD_pi_div_two] at hx
    exact capRoof_referenceCap_eq_one hx

/-- The complete niche is integrated through its three proved contact arcs.
The two contact momenta vanish by the exact matching identities. -/
theorem twice_integral_referenceNiche :
    2 * (∫ x in topLeft..topRight, referenceNiche x) =
      -(∫ t in (0 : ℝ)..(Real.pi / 2),
        cornerDensity referenceF referenceG referenceFD referenceGD t) +
      (∫ t in beta..(Real.pi / 2), momentP t ^ 2) +
      ∫ t in (0 : ℝ)..lateSwitch, momentQ t ^ 2 := by
  have h := sweptNiche_integral_eq_signed_formula isCompact_referenceHull
    beta_pos.le beta_lt_lateSwitch.le lateSwitch_lt_pi_div_two.le
    continuous_referenceNiche
    continuous_referenceF continuous_referenceG continuous_referenceFD continuous_referenceGD
    (fun t => (hasDerivAt_referenceF t).hasDerivWithinAt)
    (fun t => (hasDerivAt_referenceG t).hasDerivWithinAt)
    hasDerivWithinAt_referenceFD_right hasDerivWithinAt_referenceGD_right
    (intervalIntegrable_referenceFSecond 0 (Real.pi / 2))
    (intervalIntegrable_referenceGSecond 0 (Real.pi / 2))
    (fun t ht => angleSupport_referenceHull_eq_f ht)
    (fun t ht => by
      rw [companionNormal_eq_unitNormal]
      exact angleSupport_referenceHull_eq_g ht)
    referenceF_pi_div_two referenceG_zero
    (fun t ht => referenceF_right_curvature_le_one ht)
    (fun t ht => referenceG_right_curvature_le_one ht)
    momentP_beta momentQ_lateSwitch
    (fun t ht => momentP_nonpos_after_beta ht)
    (fun t ht => momentQ_nonneg_before_lateSwitch ht)
  rw [neg_referenceGD_zero, neg_referenceFD_pi_div_two] at h
  exact h

theorem continuous_momentP : Continuous momentP :=
  (continuous_referenceFD.sub continuous_referenceG).add continuous_const

theorem continuous_momentQ : Continuous momentQ :=
  (continuous_referenceGD.add continuous_referenceF).sub continuous_const

theorem integral_reference_negative_momentum_sq :
    (∫ t in (0 : ℝ)..(Real.pi / 2), min (momentP t) 0 ^ 2) =
      ∫ t in beta..(Real.pi / 2), momentP t ^ 2 :=
  integral_min_sq_of_sign_switch beta_pos.le beta_lt_pi_div_two.le continuous_momentP
    (fun t ht => momentP_nonneg_early ht) (fun t ht => momentP_nonpos_after_beta ht)

theorem integral_reference_positive_momentum_sq :
    (∫ t in (0 : ℝ)..(Real.pi / 2), max (momentQ t) 0 ^ 2) =
      ∫ t in (0 : ℝ)..lateSwitch, momentQ t ^ 2 :=
  integral_max_sq_of_sign_switch lateSwitch_pos.le lateSwitch_lt_pi_div_two.le continuous_momentQ
    (fun t ht => momentQ_nonneg_before_lateSwitch ht) (fun t ht => momentQ_nonpos_late ht)

/-- This identifies the analytic functional with two independently proved
geometric integrals: actual cap area minus actual niche area. -/
theorem adaptiveFunctional_reference_eq_cap_area_sub_niche :
    adaptiveFunctional referencePair = volume.real referenceCap -
      ∫ x in topLeft..topRight, referenceNiche x := by
  have hE : Continuous (fun t =>
      (referenceF t ^ 2 - referenceFD t ^ 2) +
        (referenceG t ^ 2 - referenceGD t ^ 2)) :=
    ((continuous_referenceF.pow 2).sub (continuous_referenceFD.pow 2)).add
      ((continuous_referenceG.pow 2).sub (continuous_referenceGD.pow 2))
  have hC : Continuous (cornerDensity referenceF referenceG referenceFD referenceGD) := by
    exact ((continuous_referenceF.sub continuous_const).mul continuous_momentQ).sub
      ((continuous_referenceG.sub continuous_const).mul continuous_momentP)
  have hP : Continuous (fun t => min (momentP t) 0 ^ 2) :=
    (continuous_momentP.min continuous_const).pow 2
  have hQ : Continuous (fun t => max (momentQ t) 0 ^ 2) :=
    (continuous_momentQ.max continuous_const).pow 2
  have hEi := hE.intervalIntegrable (μ := volume) 0 (Real.pi / 2)
  have hCi := hC.intervalIntegrable (μ := volume) 0 (Real.pi / 2)
  have hPi := hP.intervalIntegrable (μ := volume) 0 (Real.pi / 2)
  have hQi := hQ.intervalIntegrable (μ := volume) 0 (Real.pi / 2)
  have hsplit : 2 * adaptiveFunctional referencePair =
      (∫ t in (0 : ℝ)..(Real.pi / 2),
        (referenceF t ^ 2 - referenceFD t ^ 2) +
          (referenceG t ^ 2 - referenceGD t ^ 2)) +
      (∫ t in (0 : ℝ)..(Real.pi / 2),
        cornerDensity referenceF referenceG referenceFD referenceGD t) -
      (∫ t in (0 : ℝ)..(Real.pi / 2), min (momentP t) 0 ^ 2) -
      ∫ t in (0 : ℝ)..(Real.pi / 2), max (momentQ t) 0 ^ 2 := by
    calc
      _ = ∫ t in (0 : ℝ)..(Real.pi / 2), 2 * adaptiveDensity referencePair t := by
        rw [intervalIntegral.integral_const_mul]
        rfl
      _ = ∫ t in (0 : ℝ)..(Real.pi / 2),
          ((referenceF t ^ 2 - referenceFD t ^ 2) +
            (referenceG t ^ 2 - referenceGD t ^ 2)) +
          cornerDensity referenceF referenceG referenceFD referenceGD t -
          min (momentP t) 0 ^ 2 - max (momentQ t) 0 ^ 2 := by
        apply intervalIntegral.integral_congr
        intro t _
        unfold adaptiveDensity referencePair QuarterPair.p QuarterPair.q
          cornerDensity supportP supportQ momentP momentQ
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub ((hEi.add hCi).sub hPi) hQi,
          intervalIntegral.integral_sub (hEi.add hCi) hPi,
          intervalIntegral.integral_add hEi hCi]
  rw [integral_reference_negative_momentum_sq, integral_reference_positive_momentum_sq] at hsplit
  nlinarith [volumeReal_referenceCap_eq_support_integral, twice_integral_referenceNiche]

/-- Filling the hull downward preserves every wall in the complete niche. -/
theorem sweptNiche_referenceCap (x : ℝ) :
    sweptNiche referenceCap (Real.pi / 2) x = referenceNiche x := by
  have hvalues : sweptWallValues referenceCap (Real.pi / 2) x =
      sweptWallValues referenceHull (Real.pi / 2) x := by
    unfold sweptWallValues
    apply Set.image_congr
    intro t ht
    have hs : 0 ≤ Real.sin t :=
      (Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])).le
    have hc : 0 ≤ Real.cos t :=
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩).le
    unfold cornerWall referenceCap
    rw [firstWall_upperCap isCompact_referenceHull referenceHull_nonempty
      (fun p hp => (referenceHull_subset_unitStrip hp).1) hs x,
      secondWall_upperCap isCompact_referenceHull referenceHull_nonempty
        (fun p hp => (referenceHull_subset_unitStrip hp).1) hc x]
  change max (sSup (sweptWallValues referenceCap (Real.pi / 2) x)) 0 =
    max (sSup (sweptWallValues referenceHull (Real.pi / 2) x)) 0
  rw [hvalues]

theorem integral_topInterval_referenceNiche :
    (∫ x in topInterval, referenceNiche x) =
      ∫ x in topLeft..topRight, referenceNiche x := by
  rw [topInterval, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le topLeft_lt_topRight.le]

theorem integral_topInterval_referenceCap_roof :
    (∫ x in topInterval, capRoof referenceCap x) = capWidth referenceCap / 2 := by
  calc
    _ = ∫ _x in topInterval, (1 : ℝ) := by
      apply setIntegral_congr_fun (show MeasurableSet topInterval from measurableSet_Icc)
      intro x hx
      exact capRoof_referenceCap_eq_one hx
    _ = volume.real topInterval := by rw [setIntegral_const, smul_eq_mul, mul_one]
    _ = capWidth referenceCap / 2 := by
      rw [topInterval, Real.volume_real_Icc_of_le topLeft_lt_topRight.le, capWidth_referenceCap]
      unfold topLeft topRight
      ring

/-- The full-turn score charges the actual exterior roof and the actual
middle niche. The horizontal face contributes precisely half the width. -/
theorem capScore_referenceCap_eq_adaptiveFunctional :
    capScore referenceCap (Real.pi / 2) =
      adaptiveFunctional referencePair - capWidth referenceCap / 2 := by
  have htop : topInterval ⊆ Icc (horizontalLeft referenceCap) (horizontalRight referenceCap) := by
    rw [← middleHalfInterval_referenceCap]
    exact middleHalfInterval_subset
      (horizontalLeft_le_horizontalRight isDownwardCap_referenceCap.nonempty
        isDownwardCap_referenceCap.isCompact)
  rw [isDownwardCap_referenceCap.capScore_pi_div_two, middleHalfInterval_referenceCap,
    setIntegral_sdiff (show MeasurableSet topInterval from measurableSet_Icc)
      (isDownwardCap_referenceCap.integrableOn_capRoof_Icc _ _) htop,
    ← isDownwardCap_referenceCap.volumeReal_eq_integral_capRoof,
    integral_topInterval_referenceCap_roof]
  simp_rw [sweptNiche_referenceCap]
  rw [integral_topInterval_referenceNiche,
    adaptiveFunctional_reference_eq_cap_area_sub_niche]
  ring

/-- The reference cap attains the exact scalar value in its genuine spatial
score; this is a conclusion of the actual roof and niche calculations. -/
theorem capScore_referenceCap : capScore referenceCap (Real.pi / 2) = M / 2 := by
  rw [capScore_referenceCap_eq_adaptiveFunctional, capWidth_referenceCap,
    adaptiveFunctional_reference_eq_M_add_width]
  ring

theorem topInterval_subset_horizontalProjection_referenceHull :
    topInterval ⊆ horizontalProjection referenceHull := by
  intro x hx
  exact ⟨(x, 1), topFace_mem_referenceHull hx, rfl⟩

theorem integral_projection_referenceNiche :
    (∫ x in horizontalProjection referenceHull, referenceNiche x) =
      ∫ x in topLeft..topRight, referenceNiche x := by
  rw [setIntegral_eq_subset_of_zero_off
    (isCompact_horizontalProjection isCompact_referenceHull).measurableSet
    (show MeasurableSet topInterval from measurableSet_Icc)
    (continuous_referenceNiche.continuousOn.integrableOn_compact
      (isCompact_horizontalProjection isCompact_referenceHull))
    topInterval_subset_horizontalProjection_referenceHull
    (fun x hx => referenceNiche_eq_zero_outside hx.2)]
  exact integral_topInterval_referenceNiche

/-- Cavalieri is applied to the concrete retained body. Reflection supplies
the lower hull wall, the strict midline margin prevents empty fibers, and
the top-face support restriction removes every overlap correction. -/
theorem volumeReal_referenceSofa : volume.real referenceSofa = M := by
  have hseparate : ∀ x ∈ horizontalProjection referenceHull,
      capRoof (upperCap referenceHull) x = 1 ∨ referenceNiche x = 0 := by
    intro x _
    by_cases hx : x ∈ topInterval
    · exact Or.inl (capRoof_referenceCap_eq_one hx)
    · exact Or.inr (referenceNiche_eq_zero_outside hx)
  have harea := volumeReal_symmetricTrim_eq_cap_area referenceHull_nonempty
    isCompact_referenceHull convex_referenceHull referenceHull_subset_unitStrip
    (fun p hp => (reflect_mem_referenceHull p).mpr hp) continuous_referenceNiche
    (fun x _ => referenceNiche_nonneg x) (fun x _ => (referenceNiche_lt_half x).le)
    hseparate
  change volume.real referenceSofa = 2 * volume.real referenceCap -
    capWidth referenceCap - 2 * ∫ x in horizontalProjection referenceHull, referenceNiche x at harea
  rw [integral_projection_referenceNiche, capWidth_referenceCap] at harea
  nlinarith [adaptiveFunctional_reference_eq_cap_area_sub_niche,
    twice_adaptiveFunctional_reference_sub_width]

theorem volume_referenceSofa : volume referenceSofa = ENNReal.ofReal M := by
  rw [← volumeReal_referenceSofa]
  exact (ENNReal.ofReal_toReal isCompact_referenceSofa.measure_ne_top).symm

end AmbidextrousSofa.Reference
