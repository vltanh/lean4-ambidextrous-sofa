module

public import AmbidextrousSofa.Analysis.TiltedMomentumConvolution

@[expose] public section

/-!
# Exact harmonic first-floor and right-window moments

The cosine self-interaction is evaluated by applying the absolutely
continuous fundamental theorem to the squared sine and cosine
primitives. Together with the actual momentum reconstruction, this
calculates the two weighted momentum integrals and their literal sine
remainders.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa.Analysis

theorem forward_cosine_self_interaction
    {r : ℝ → ℝ} {a b : ℝ} (hr : IntervalIntegrable r volume a b) :
    (∫ t in a..b, r t * forwardCosineConvolution r a t) =
      1 / 2 * ((∫ t in a..b, r t * Real.cos t) ^ 2 +
        (∫ t in a..b, r t * Real.sin t) ^ 2) := by
  have hcos := hr.mul_continuousOn Real.continuous_cos.continuousOn
  have hsin := hr.mul_continuousOn Real.continuous_sin.continuousOn
  have hA := hcos.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
  have hB := hsin.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
  rw [ac_intervalIntegral_eq_sub_of_ae_hasDerivAt ((absolutelyContinuousOnInterval_const_real
    (1 / 2) a b).fun_mul ((hA.fun_mul hA).fun_add (hB.fun_mul hB))) ?_]
  · simp; ring
  filter_upwards [hcos.ae_hasDerivAt_integral, hsin.ae_hasDerivAt_integral] with t hct hst ht
  have hA' := hct ht a (by simp)
  have hB' := hst ht a (by simp)
  refine (((hA'.fun_mul hA').fun_add (hB'.fun_mul hB')).const_mul (1 / 2)).congr_deriv ?_
  rw [forwardCosineConvolution_eq_moments (hr.mono_set (uIcc_subset_uIcc_left ht))]
  ring

theorem backward_cosine_self_interaction
    {r : ℝ → ℝ} {a b : ℝ} (hr : IntervalIntegrable r volume a b) :
    (∫ t in a..b, r t * backwardCosineConvolution r b t) =
      1 / 2 * ((∫ t in a..b, r t * Real.cos t) ^ 2 +
        (∫ t in a..b, r t * Real.sin t) ^ 2) := by
  have hcos := hr.mul_continuousOn Real.continuous_cos.continuousOn
  have hsin := hr.mul_continuousOn Real.continuous_sin.continuousOn
  have hA := hcos.absolutelyContinuousOnInterval_intervalIntegral (c := b) (by simp)
  have hB := hsin.absolutelyContinuousOnInterval_intervalIntegral (c := b) (by simp)
  have hi := ac_intervalIntegral_eq_sub_of_ae_hasDerivAt
    (F := fun t => -(r t * backwardCosineConvolution r b t))
    ((absolutelyContinuousOnInterval_const_real (1 / 2) a b).fun_mul
      ((hA.fun_mul hA).fun_add (hB.fun_mul hB))) ?_
  · rw [intervalIntegral.integral_neg, intervalIntegral.integral_symm a b,
      intervalIntegral.integral_symm a b] at hi
    simp at hi
    linarith
  filter_upwards [hcos.ae_hasDerivAt_integral, hsin.ae_hasDerivAt_integral] with t hct hst ht
  have hA' := hct ht b (by simp)
  have hB' := hst ht b (by simp)
  refine (((hA'.fun_mul hA').fun_add (hB'.fun_mul hB')).const_mul (1 / 2)).congr_deriv ?_
  rw [backwardCosineConvolution_eq_moments (hr.mono_set (uIcc_subset_uIcc_right ht)),
    intervalIntegral.integral_symm t b, intervalIntegral.integral_symm t b]
  ring

theorem firstUnit_initial_harmonic_moment
    {p q u v : ℝ → ℝ} {γ C S h eR : ℝ} (hγ : 0 ≤ γ)
    (hp : AbsolutelyContinuousOnInterval p 0 γ)
    (hq : AbsolutelyContinuousOnInterval q 0 γ)
    (hu : IntervalIntegrable u volume 0 γ) (hv : IntervalIntegrable v volume 0 γ)
    (hode : ∀ᵐ t ∂volume.restrict (Icc 0 γ),
      HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t)
    (hp0 : p 0 = eR + h) (hq0 : q 0 = 3 * C - 1)
    (hS : (∫ t in 0..γ, (1 - v t) * Real.cos t) = S)
    (hh : (∫ t in 0..γ, (1 - v t) * Real.sin t) = h) :
    (∫ t in 0..γ, (q t + 1) * (1 - v t)) =
      3 * C * S - S ^ 2 / 2 + eR * h + h ^ 2 / 2 +
        firstUnitLeftRemainder (fun t => 1 - v t) u γ := by
  have hr : IntervalIntegrable (fun t => 1 - v t) volume 0 γ := intervalIntegrable_const.sub hv
  have hrc := (hr.mul_continuousOn Real.continuous_cos.continuousOn).const_mul (3 * C)
  have hrs := (hr.mul_continuousOn Real.continuous_sin.continuousOn).const_mul (eR + h)
  have hru := hr.mul_continuousOn
    (absolutelyContinuousOnInterval_forwardSineConvolution hγ hu).continuousOn
  have hrr := hr.mul_continuousOn
    (absolutelyContinuousOnInterval_forwardCosineConvolution hγ hr).continuousOn
  calc
    _ = ∫ t in 0..γ, 3 * C * ((1 - v t) * Real.cos t) + (eR + h) * ((1 - v t) * Real.sin t) +
          (1 - v t) * forwardSineConvolution u 0 t -
            (1 - v t) * forwardCosineConvolution (fun t => 1 - v t) 0 t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      have hsub : uIcc 0 t ⊆ uIcc 0 γ := uIcc_subset_uIcc_left ht
      rw [uIcc_of_le hγ] at ht
      have heq := secondMomentum_forward_convolution ht.1 (hp.mono hsub) (hq.mono hsub)
        (hu.mono_set hsub) (hv.mono_set hsub) (ae_restrict_Icc_subinterval le_rfl ht.2 hode)
      have hc := forwardCosineConvolution_add_complement (hv.mono_set hsub)
      linear_combination (1 - v t) * (heq + hc + Real.sin t * hp0 + Real.cos t * hq0)
    _ = _ := by
      rw [intervalIntegral.integral_sub ((hrc.add hrs).add hru) hrr,
        intervalIntegral.integral_add (hrc.add hrs) hru, intervalIntegral.integral_add hrc hrs,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        forward_cosine_self_interaction hr, hS, hh, firstUnitLeftRemainder]
      ring

theorem firstUnit_right_harmonic_moment
    {p q u v : ℝ → ℝ} {β C T z eL : ℝ} (hβ : β ≤ Real.pi / 2)
    (hp : AbsolutelyContinuousOnInterval p β (Real.pi / 2))
    (hq : AbsolutelyContinuousOnInterval q β (Real.pi / 2))
    (hu : IntervalIntegrable u volume β (Real.pi / 2))
    (hv : IntervalIntegrable v volume β (Real.pi / 2))
    (hode : ∀ᵐ t ∂volume.restrict (Icc β (Real.pi / 2)),
      HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t)
    (hpL : p (Real.pi / 2) = 1 - 3 * C - T) (hqL : q (Real.pi / 2) = -eL)
    (hT : (∫ t in β..(Real.pi / 2), (1 - u t) * Real.sin t) = T)
    (hz : (∫ t in β..(Real.pi / 2), (1 - u t) * Real.cos t) = z) :
    (∫ t in β..(Real.pi / 2), firstUnitGainDensity (p t) (u t)) =
      3 * C * T + T ^ 2 / 2 + eL * z - z ^ 2 / 2 +
        firstUnitRightRemainder (fun t => 1 - u t) v β (Real.pi / 2) := by
  have hr : IntervalIntegrable (fun t => 1 - u t) volume β (Real.pi / 2) :=
    intervalIntegrable_const.sub hu
  have hrs := (hr.mul_continuousOn Real.continuous_sin.continuousOn).const_mul (3 * C + T)
  have hrc := (hr.mul_continuousOn Real.continuous_cos.continuousOn).const_mul eL
  have hrv := hr.mul_continuousOn
    (absolutelyContinuousOnInterval_backwardSineConvolution hβ hv).continuousOn
  have hrr := hr.mul_continuousOn
    (absolutelyContinuousOnInterval_backwardCosineConvolution hβ hr).continuousOn
  calc
    _ = ∫ t in β..(Real.pi / 2), (3 * C + T) * ((1 - u t) * Real.sin t) +
          eL * ((1 - u t) * Real.cos t) + (1 - u t) * backwardSineConvolution v (Real.pi / 2) t -
            (1 - u t) * backwardCosineConvolution (fun t => 1 - u t) (Real.pi / 2) t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      have hsub : uIcc t (Real.pi / 2) ⊆ uIcc β (Real.pi / 2) := uIcc_subset_uIcc_right ht
      rw [uIcc_of_le hβ] at ht
      have heq := firstMomentum_backward_convolution ht.2 (hp.mono hsub) (hq.mono hsub)
        (hu.mono_set hsub) (hv.mono_set hsub) (ae_restrict_Icc_subinterval ht.1 le_rfl hode)
      have hc := backwardCosineConvolution_add_complement (hu.mono_set hsub)
      unfold firstUnitGainDensity
      linear_combination (1 - u t) * (heq + hc - Real.sin t * hpL - Real.cos t * hqL)
    _ = _ := by
      rw [intervalIntegral.integral_sub ((hrs.add hrc).add hrv) hrr,
        intervalIntegral.integral_add (hrs.add hrc) hrv, intervalIntegral.integral_add hrs hrc,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        backward_cosine_self_interaction hr, hT, hz, firstUnitRightRemainder]
      ring

end AmbidextrousSofa.Analysis
