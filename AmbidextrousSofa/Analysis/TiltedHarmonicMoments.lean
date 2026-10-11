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

/-- The cosine self-interaction of a density, with the convolution based at any point `c`, is the
change of half the squared moment vector. -/
theorem integral_mul_forwardCosineConvolution {r : ℝ → ℝ} {a b c : ℝ}
    (hr : IntervalIntegrable r volume a b) (hc : c ∈ uIcc a b) :
    (∫ t in a..b, r t * forwardCosineConvolution r c t) =
      ((∫ s in c..b, r s * Real.cos s) ^ 2 + (∫ s in c..b, r s * Real.sin s) ^ 2 -
        (∫ s in c..a, r s * Real.cos s) ^ 2 - (∫ s in c..a, r s * Real.sin s) ^ 2) / 2 := by
  have hcos := hr.mul_continuousOn Real.continuous_cos.continuousOn
  have hsin := hr.mul_continuousOn Real.continuous_sin.continuousOn
  have hA := hcos.absolutelyContinuousOnInterval_intervalIntegral hc
  have hB := hsin.absolutelyContinuousOnInterval_intervalIntegral hc
  rw [ac_intervalIntegral_eq_sub_of_ae_hasDerivAt ((absolutelyContinuousOnInterval_const_real
    (1 / 2) a b).fun_mul ((hA.fun_mul hA).fun_add (hB.fun_mul hB))) ?_]
  · ring
  filter_upwards [hcos.ae_hasDerivAt_integral, hsin.ae_hasDerivAt_integral] with t hct hst ht
  have hA' := hct ht c hc
  have hB' := hst ht c hc
  refine (((hA'.fun_mul hA').fun_add (hB'.fun_mul hB')).const_mul (1 / 2)).congr_deriv ?_
  rw [forwardCosineConvolution_eq_moments (hr.mono_set (uIcc_subset_uIcc hc ht))]
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
  have hru := hr.mul_continuousOn (continuousOn_forwardSineConvolution hu left_mem_uIcc)
  have hrr := hr.mul_continuousOn (continuousOn_forwardCosineConvolution hr left_mem_uIcc)
  calc
    _ = ∫ t in 0..γ, 3 * C * ((1 - v t) * Real.cos t) + (eR + h) * ((1 - v t) * Real.sin t) +
          (1 - v t) * forwardSineConvolution u 0 t -
            (1 - v t) * forwardCosineConvolution (fun t => 1 - v t) 0 t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      have hsub : uIcc 0 t ⊆ uIcc 0 γ := uIcc_subset_uIcc_left ht
      rw [uIcc_of_le hγ] at ht
      have heq := (momentum_reconstruction ht.1 (hp.mono hsub) (hq.mono hsub)
        (hu.mono_set hsub) (hv.mono_set hsub) (ae_restrict_Icc_subinterval le_rfl ht.2 hode)).1
      have hc := forwardCosineConvolution_add_complement (hv.mono_set hsub)
      rw [sub_zero] at heq hc
      linear_combination (1 - v t) * (heq + hc + Real.sin t * hp0 + Real.cos t * hq0)
    _ = _ := by
      rw [intervalIntegral.integral_sub ((hrc.add hrs).add hru) hrr,
        intervalIntegral.integral_add (hrc.add hrs) hru, intervalIntegral.integral_add hrc hrs,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        integral_mul_forwardCosineConvolution hr left_mem_uIcc, hS, hh, firstUnitLeftRemainder]
      simp only [intervalIntegral.integral_same]
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
  have hrv := hr.mul_continuousOn (continuousOn_forwardSineConvolution hv right_mem_uIcc)
  have hrr := hr.mul_continuousOn (continuousOn_forwardCosineConvolution hr right_mem_uIcc)
  calc
    _ = ∫ t in β..(Real.pi / 2), (3 * C + T) * ((1 - u t) * Real.sin t) +
          eL * ((1 - u t) * Real.cos t) + (1 - u t) * forwardSineConvolution v (Real.pi / 2) t +
            (1 - u t) * forwardCosineConvolution (fun t => 1 - u t) (Real.pi / 2) t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      have hsub : uIcc t (Real.pi / 2) ⊆ uIcc β (Real.pi / 2) := uIcc_subset_uIcc_right ht
      rw [uIcc_of_le hβ] at ht
      have heq := (momentum_reconstruction ht.2 (hp.mono hsub) (hq.mono hsub)
        (hu.mono_set hsub) (hv.mono_set hsub) (ae_restrict_Icc_subinterval ht.1 le_rfl hode)).2
      have hc := forwardCosineConvolution_add_complement (hu.mono_set hsub).symm
      rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub] at heq
      rw [Real.sin_sub_pi_div_two] at hc
      unfold firstUnitGainDensity
      linear_combination (1 - u t) * (-heq - hc - Real.sin t * hpL - Real.cos t * hqL)
    _ = _ := by
      rw [intervalIntegral.integral_add ((hrs.add hrc).add hrv) hrr,
        intervalIntegral.integral_add (hrs.add hrc) hrv, intervalIntegral.integral_add hrs hrc,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        integral_mul_forwardCosineConvolution hr right_mem_uIcc, intervalIntegral.integral_symm β,
        intervalIntegral.integral_symm β, hT, hz, firstUnitRightRemainder,
        backwardSineConvolution_eq_forward]
      simp only [intervalIntegral.integral_same]
      ring

end AmbidextrousSofa.Analysis
