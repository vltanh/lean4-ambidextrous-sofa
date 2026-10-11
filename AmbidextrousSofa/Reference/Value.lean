module

public import AmbidextrousSofa.Reference.Stationarity
public import AmbidextrousSofa.Reference.Body
public import AmbidextrousSofa.Measure.SignedRoofIntegralAC
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

attribute [local fun_prop] continuous_referenceF continuous_referenceG continuous_referenceFD
  continuous_referenceGD

/-- Subtracting the self-variation leaves only the linear and constant
parts of the active phase quadratic. The formula is valid at the contacts. -/
theorem twice_density_sub_self_variation (u : QuarterPair) (t : ℝ) :
    2 * adaptiveDensity u t - adaptiveLinearDensity u u t =
      2 - u.f t - u.g t + (u.fD t - u.gD t) / 2 - min (u.p t) 0 + max (u.q t) 0 := by
  simp only [adaptiveDensity, adaptiveLinearDensity, min_def, max_def, QuarterPair.p,
    QuarterPair.q]
  split_ifs <;> ring

/-- The density `2 * adaptiveDensity - adaptiveLinearDensity` of the reference pair. -/
def referenceValueRemainder (t : ℝ) : ℝ :=
  2 - referenceF t - referenceG t + (referenceFD t - referenceGD t) / 2 -
    min (momentP t) 0 + max (momentQ t) 0

/-- The three phase integrals of the remainder have elementary antiderivatives. -/
theorem integral_referenceValueRemainder :
    (∫ t in (0 : ℝ)..(Real.pi / 2), referenceValueRemainder t) =
      4 * A * cosBeta - 8 / 3 * A - 1 + beta := by
  have hi (a b : ℝ) : IntervalIntegrable referenceValueRemainder volume a b := by
    unfold referenceValueRemainder momentP momentQ
    exact Continuous.intervalIntegrable (by fun_prop) a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 lateSwitch) (hi _ _),
    ← intervalIntegral.integral_add_adjacent_intervals (hi 0 beta) (hi _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le beta_pos.le (f := fun t =>
      t / 2 + (2 * A - 1 / 4) * Real.cos t + (A - 3 / 4) * Real.sin t) (by fun_prop) ?_ (hi _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le beta_lt_lateSwitch.le
      (f := fun t => (referenceG t - referenceF t) / 2) (by fun_prop) ?_ (hi _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le lateSwitch_lt_pi_div_two.le (f := fun t =>
      t / 2 - (1 / 4 - A / 3) * Real.cos t - (3 / 4 + 2 / 3 * A) * Real.sin t) (by fun_prop) ?_
      (hi _ _)]
  · simp only [referenceF, referenceG, le_refl, ite_true, not_le.mpr beta_lt_lateSwitch, ite_false,
      f_matching_last, g_matching_last]
    simp only [fEarly, gEarly, fLate, gLate, lateSwitch, Real.sin_zero, Real.cos_zero,
      Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub,
      cosBeta]
    ring
  · intro t ht
    rw [referenceValueRemainder,
      min_eq_left (momentP_nonpos_after_beta ⟨beta_lt_lateSwitch.le.trans ht.1.le, ht.2.le⟩),
      max_eq_right (momentQ_nonpos_late ⟨ht.1.le, ht.2.le⟩)]
    simp only [momentP, referenceF, referenceG, referenceFD, referenceGD,
      not_le.mpr (beta_lt_lateSwitch.trans ht.1), not_le.mpr ht.1, ite_false, fLate, gLate, fLateD,
      gLateD]
    exact ((((hasDerivAt_id t).div_const 2).sub ((Real.hasDerivAt_cos t).const_mul _)).sub
      ((Real.hasDerivAt_sin t).const_mul _)).congr_deriv (by ring)
  · intro t ht
    rw [referenceValueRemainder,
      min_eq_left (momentP_nonpos_after_beta ⟨ht.1.le, ht.2.le.trans lateSwitch_lt_pi_div_two.le⟩),
      max_eq_left (momentQ_nonneg_before_lateSwitch ⟨beta_pos.le.trans ht.1.le, ht.2.le⟩)]
    exact (((hasDerivAt_referenceG t).sub (hasDerivAt_referenceF t)).div_const 2).congr_deriv
      (by unfold momentP momentQ; ring)
  · intro t ht
    rw [referenceValueRemainder, min_eq_right (momentP_nonneg_early ⟨ht.1.le, ht.2.le⟩),
      max_eq_left (momentQ_nonneg_before_lateSwitch ⟨ht.1.le, ht.2.le.trans beta_lt_lateSwitch.le⟩)]
    simp only [momentQ, referenceF, referenceG, referenceFD, referenceGD, ht.2.le, ite_true,
      fEarly, gEarly, fEarlyD, gEarlyD]
    exact ((((hasDerivAt_id t).div_const 2).add ((Real.hasDerivAt_cos t).const_mul _)).add
      ((Real.hasDerivAt_sin t).const_mul _)).congr_deriv (by ring)

/-- The actual self-variation is evaluated by the four endpoint fluxes. -/
theorem reference_self_variation :
    adaptiveFirstVariation referencePair referencePair = 16 / 3 * A - 1 := by
  rw [adaptiveFirstVariation_eq_boundary referencePair referencePair
    (fun _ => referencePair_eulerF) (fun _ => referencePair_eulerG)]
  simp only [QuarterPair.fluxF, QuarterPair.fluxG]
  rw [min_eq_left (show referencePair.p (Real.pi / 2) ≤ 0 from
      momentP_nonpos_after_beta ⟨beta_lt_pi_div_two.le, le_rfl⟩),
    min_eq_right (show 0 ≤ referencePair.p 0 from momentP_nonneg_early ⟨le_rfl, beta_pos.le⟩),
    max_eq_right (show referencePair.q (Real.pi / 2) ≤ 0 from
      momentQ_nonpos_late ⟨lateSwitch_lt_pi_div_two.le, le_rfl⟩),
    max_eq_left (show 0 ≤ referencePair.q 0 from
      momentQ_nonneg_before_lateSwitch ⟨le_rfl, lateSwitch_pos.le⟩)]
  simp only [QuarterPair.p, QuarterPair.q, referencePair, referenceF_zero, referenceG_zero,
    referenceF_pi_div_two, referenceG_pi_div_two, referenceFD_zero, referenceGD_zero,
    referenceFD_pi_div_two, referenceGD_pi_div_two]
  ring

/-- The width term is still present in the support functional. -/
theorem adaptiveFunctional_reference_eq_M_add_width :
    adaptiveFunctional referencePair = (M + 8 / 3 * A) / 2 := by
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have h : ∫ t in (0 : ℝ)..(Real.pi / 2), (2 * adaptiveDensity referencePair t -
      adaptiveLinearDensity referencePair referencePair t) =
      4 * A * cosBeta - 8 / 3 * A - 1 + beta :=
    (intervalIntegral.integral_congr fun t _ =>
      twice_density_sub_self_variation referencePair t).trans integral_referenceValueRemainder
  rw [intervalIntegral.integral_sub
    (((continuousOn_adaptiveDensity referencePair).intervalIntegrable_of_Icc hL).const_mul 2)
    ((continuousOn_adaptiveLinearDensity referencePair referencePair).intervalIntegrable_of_Icc hL),
    intervalIntegral.integral_const_mul, ← adaptiveFunctional, ← adaptiveFirstVariation,
    reference_self_variation] at h
  have hY : 4 * A * cosBeta = M - beta + 2 := by
    rw [mul_assoc, A_mul_cosBeta, eq_div_of_mul_eq Y_ne_zero M_sub_beta_add_two_mul_Y]
    ring
  linarith

/-- A finite measurable phase switch preserves interval integrability. This
allows the actual right second derivatives to jump at both contacts. -/
theorem intervalIntegrable_if_lt {a b c : ℝ} {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable (fun t => if t < c then f t else g t) volume a b := by
  rw [intervalIntegrable_iff] at hf hg ⊢
  exact Integrable.piecewise (s := Iio c) measurableSet_Iio hf.integrableOn hg.integrableOn

theorem neg_referenceGD_zero : -referenceGD 0 = topLeft := by
  rw [referenceGD_zero, topLeft]; ring

theorem neg_referenceFD_pi_div_two : -referenceFD (Real.pi / 2) = topRight := by
  rw [referenceFD_pi_div_two, topRight]; ring

/-- This identifies the analytic functional with two independently proved
geometric integrals: actual cap area minus actual niche area. The cap area is
obtained from actual roof points on both arcs and the realized top face, and
the niche is integrated through its three proved contact arcs. -/
theorem adaptiveFunctional_reference_eq_cap_area_sub_niche :
    adaptiveFunctional referencePair = volume.real referenceCap -
      ∫ x in topLeft..topRight, referenceNiche x := by
  have hF := continuous_referenceF; have hG := continuous_referenceG
  have hFD := continuous_referenceFD; have hGD := continuous_referenceGD
  have hI {f : ℝ → ℝ} (hf : Continuous f) : IntervalIntegrable f volume 0 (Real.pi / 2) :=
    hf.intervalIntegrable _ _
  have hFs : IntervalIntegrable referenceFSecond volume 0 (Real.pi / 2) :=
    intervalIntegrable_if_lt (hI (by fun_prop)) (intervalIntegrable_if_lt (hI (by fun_prop))
      (hI (by fun_prop)))
  have hGs : IntervalIntegrable referenceGSecond volume 0 (Real.pi / 2) :=
    intervalIntegrable_if_lt (hI (by fun_prop)) (intervalIntegrable_if_lt (hI (by fun_prop))
      (hI (by fun_prop)))
  have hFDac := absolutelyContinuousOnInterval_of_hasDerivWithinAt_Ioi hFD
    hasDerivWithinAt_referenceFD_right hFs
  have hGDac := absolutelyContinuousOnInterval_of_hasDerivWithinAt_Ioi hGD
    hasDerivWithinAt_referenceGD_right hGs
  have harea := isDownwardCap_referenceCap.volumeReal_eq_support_energy_ac
    (absolutelyContinuousOnInterval_of_hasDerivWithinAt_Ioi hF
      (fun t => (hasDerivAt_referenceF t).hasDerivWithinAt) (hI hFD))
    (absolutelyContinuousOnInterval_of_hasDerivWithinAt_Ioi hG
      (fun t => (hasDerivAt_referenceG t).hasDerivWithinAt) (hI hGD)) hFDac hGDac
    (.of_forall hasDerivAt_referenceF) (.of_forall hasDerivAt_referenceG)
    (ae_hasDerivAt_of_hasDerivWithinAt_Ioi hFDac hasDerivWithinAt_referenceFD_right)
    (ae_hasDerivAt_of_hasDerivWithinAt_Ioi hGDac hasDerivWithinAt_referenceGD_right) hFs hGs
    (fun _ ht => referenceHull_subset_referenceCap (fBoundary_mem_referenceHull ht))
    (fun _ ht => referenceHull_subset_referenceCap (gBoundary_mem_referenceHull ht))
    (fun _ ht => angleSupport_referenceCap_eq_f ⟨ht.1.le, ht.2.le⟩)
    (fun _ ht => angleSupport_referenceCap_eq_g ⟨ht.1.le, ht.2.le⟩)
    (by rw [horizontalLeft_referenceCap, referenceG_pi_div_two]; ring)
    (by rw [horizontalRight_referenceCap, referenceF_zero]) referenceF_pi_div_two referenceG_zero
    (by rw [neg_referenceGD_zero, neg_referenceFD_pi_div_two]; exact topLeft_lt_topRight.le)
    (fun x hx => capRoof_referenceCap_eq_one
      (by rwa [neg_referenceGD_zero, neg_referenceFD_pi_div_two] at hx))
  have hniche := sweptNiche_integral_eq_signed_formula isCompact_referenceHull
    beta_pos.le beta_lt_lateSwitch.le lateSwitch_lt_pi_div_two.le continuous_referenceNiche
    hF hG hFD hGD (fun t => (hasDerivAt_referenceF t).hasDerivWithinAt)
    (fun t => (hasDerivAt_referenceG t).hasDerivWithinAt)
    hasDerivWithinAt_referenceFD_right hasDerivWithinAt_referenceGD_right hFs hGs
    (fun _ => angleSupport_referenceHull_eq_f)
    (fun t ht => companionNormal_eq_unitNormal t ▸ angleSupport_referenceHull_eq_g ht)
    referenceF_pi_div_two referenceG_zero
    (fun t _ => (referenceF_right_curvature t).2.le)
    (fun t _ => referenceG_right_curvature_le_one t)
    momentP_beta momentQ_lateSwitch (fun _ => momentP_nonpos_after_beta)
    (fun _ => momentQ_nonneg_before_lateSwitch)
  rw [neg_referenceGD_zero, neg_referenceFD_pi_div_two] at hniche
  have hP : Continuous (supportP referenceFD referenceG) := by unfold supportP; fun_prop
  have hQ : Continuous (supportQ referenceGD referenceF) := by unfold supportQ; fun_prop
  have hC : Continuous (cornerDensity referenceF referenceG referenceFD referenceGD) := by
    unfold cornerDensity; fun_prop
  have hsplit : 2 * adaptiveFunctional referencePair = ∫ t in (0 : ℝ)..(Real.pi / 2),
      ((referenceF t ^ 2 - referenceFD t ^ 2) + (referenceG t ^ 2 - referenceGD t ^ 2) +
        cornerDensity referenceF referenceG referenceFD referenceGD t -
        min (supportP referenceFD referenceG t) 0 ^ 2) -
        max (supportQ referenceGD referenceF t) 0 ^ 2 := by
    rw [adaptiveFunctional, ← intervalIntegral.integral_const_mul]
    congr 1
    ext t
    simp only [adaptiveDensity, referencePair, QuarterPair.p, QuarterPair.q, cornerDensity,
      supportP, supportQ]
    ring
  rw [intervalIntegral.integral_sub (hI ?_) (hI ?_), intervalIntegral.integral_sub (hI ?_) (hI ?_),
    intervalIntegral.integral_add (hI ?_) (hI ?_),
    integral_min_sq_of_sign_switch beta_pos.le beta_lt_pi_div_two.le hP
      (fun _ => momentP_nonneg_early) (fun _ => momentP_nonpos_after_beta),
    integral_max_sq_of_sign_switch lateSwitch_pos.le lateSwitch_lt_pi_div_two.le hQ
      (fun _ => momentQ_nonneg_before_lateSwitch) (fun _ => momentQ_nonpos_late)] at hsplit
  · unfold referenceNiche
    linarith
  all_goals fun_prop

/-- Filling the hull downward preserves every wall in the complete niche. -/
theorem sweptNiche_referenceCap (x : ℝ) :
    sweptNiche referenceCap (Real.pi / 2) x = referenceNiche x := by
  have h0 : ∀ p ∈ referenceHull, 0 ≤ p.2 := fun _ hp => (referenceHull_subset_unitStrip hp).1
  unfold referenceNiche sweptNiche sweptWallValues
  congr 2
  refine image_congr fun t ht => ?_
  rw [cornerWall, cornerWall, referenceCap,
    firstWall_upperCap isCompact_referenceHull referenceHull_nonempty h0
      (Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le (by linarith [ht.2, Real.pi_pos])) x,
    secondWall_upperCap isCompact_referenceHull referenceHull_nonempty h0
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2.le⟩) x]

theorem integral_topInterval_referenceNiche :
    (∫ x in topInterval, referenceNiche x) =
      ∫ x in topLeft..topRight, referenceNiche x := by
  rw [topInterval, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le topLeft_lt_topRight.le]

/-- The reference cap attains the exact scalar value in its genuine spatial
score; this is a conclusion of the actual roof and niche calculations. -/
theorem capScore_referenceCap : capScore referenceCap (Real.pi / 2) = M / 2 := by
  have htop : topInterval ⊆ Icc (horizontalLeft referenceCap) (horizontalRight referenceCap) := by
    rw [← middleHalfInterval_referenceCap]
    exact middleHalfInterval_subset (horizontalLeft_le_horizontalRight
      isDownwardCap_referenceCap.nonempty isDownwardCap_referenceCap.isCompact)
  have hroof : ∫ x in topInterval, capRoof referenceCap x = 4 / 3 * A := by
    rw [setIntegral_congr_fun (s := topInterval) measurableSet_Icc
      fun x hx => capRoof_referenceCap_eq_one hx, setIntegral_const, smul_eq_mul, mul_one,
      topInterval, Real.volume_real_Icc_of_le topLeft_lt_topRight.le, topLeft, topRight]
    ring
  rw [isDownwardCap_referenceCap.capScore_pi_div_two, middleHalfInterval_referenceCap,
    setIntegral_sdiff (t := topInterval) measurableSet_Icc
      (isDownwardCap_referenceCap.integrableOn_capRoof_Icc _ _) htop,
    ← isDownwardCap_referenceCap.volumeReal_eq_integral_capRoof, hroof]
  simp_rw [sweptNiche_referenceCap]
  rw [integral_topInterval_referenceNiche]
  linarith [adaptiveFunctional_reference_eq_cap_area_sub_niche,
    adaptiveFunctional_reference_eq_M_add_width]

/-- Cavalieri is applied to the concrete retained body. Reflection supplies
the lower hull wall, the strict midline margin prevents empty fibers, and
the top-face support restriction removes every overlap correction. -/
theorem volumeReal_referenceSofa : volume.real referenceSofa = M := by
  have harea := volumeReal_symmetricTrim_eq_cap_area referenceHull_nonempty
    isCompact_referenceHull convex_referenceHull referenceHull_subset_unitStrip
    (fun p hp => (reflect_mem_referenceHull p).mpr hp) continuous_referenceNiche
    (fun x _ => referenceNiche_nonneg x) (fun x _ => (referenceNiche_lt_half x).le)
    fun x _ => (em (x ∈ topInterval)).imp capRoof_referenceCap_eq_one
      referenceNiche_eq_zero_outside
  change volume.real referenceSofa = 2 * volume.real referenceCap -
    capWidth referenceCap - 2 * ∫ x in horizontalProjection referenceHull, referenceNiche x at harea
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (isCompact_horizontalProjection isCompact_referenceHull).measurableSet
    (fun x hx => ⟨(x, 1), topFace_mem_referenceHull hx, rfl⟩)
    (fun x hx => referenceNiche_eq_zero_outside hx.2), integral_topInterval_referenceNiche,
    capWidth_referenceCap] at harea
  linarith [adaptiveFunctional_reference_eq_cap_area_sub_niche,
    adaptiveFunctional_reference_eq_M_add_width]

theorem volume_referenceSofa : volume referenceSofa = ENNReal.ofReal M := by
  rw [← volumeReal_referenceSofa]
  exact (ENNReal.ofReal_toReal isCompact_referenceSofa.measure_ne_top).symm

end AmbidextrousSofa.Reference
