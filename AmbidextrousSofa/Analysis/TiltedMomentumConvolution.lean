module

public import AmbidextrousSofa.Analysis.TiltedFirstUnitMoments

@[expose] public section

/-!
# Harmonic reconstruction from the actual momentum ODE

The rotating coordinates remove the homogeneous quarter-turn dynamics.
Their absolutely continuous fundamental theorem gives the literal sine
and cosine convolutions used in the first-floor energy identities.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa.Analysis

def forwardCosineConvolution (r : ℝ → ℝ) (a t : ℝ) : ℝ :=
  ∫ s in a..t, r s * Real.cos (t - s)

def backwardCosineConvolution (r : ℝ → ℝ) (b t : ℝ) : ℝ :=
  ∫ s in t..b, r s * Real.cos (s - t)

def momentumRotX (p q : ℝ → ℝ) (t : ℝ) : ℝ :=
  (p t - 1) * Real.cos t + (q t + 1) * Real.sin t

def momentumRotY (p q : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(p t - 1) * Real.sin t + (q t + 1) * Real.cos t

theorem ac_intervalIntegral_eq_sub_of_ae_hasDerivAt
    {E F : ℝ → ℝ} {a b : ℝ}
    (hE : AbsolutelyContinuousOnInterval E a b)
    (hD : ∀ᵐ t ∂volume, t ∈ uIcc a b → HasDerivAt E (F t) t) :
    (∫ t in a..b, F t) = E b - E a := by
  rw [← hE.integral_deriv_eq_sub]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hD] with t ht hmem using (ht (Ioc_subset_Icc_self hmem)).deriv.symm

theorem momentum_rotation_integrals
    {p q u v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hp : AbsolutelyContinuousOnInterval p a b)
    (hq : AbsolutelyContinuousOnInterval q a b)
    (hu : IntervalIntegrable u volume a b) (hv : IntervalIntegrable v volume a b)
    (hode : ∀ᵐ t ∂volume.restrict (Icc a b),
      HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t) :
    (∫ t in a..b, u t * Real.cos t) + (∫ t in a..b, v t * Real.sin t) =
      momentumRotX p q b - momentumRotX p q a ∧
    (∫ t in a..b, v t * Real.cos t) - (∫ t in a..b, u t * Real.sin t) =
      momentumRotY p q b - momentumRotY p q a := by
  have hc := Real.contDiff_cos.contDiffOn.absolutelyContinuousOnInterval (a := a) (b := b)
  have hs := Real.contDiff_sin.contDiffOn.absolutelyContinuousOnInterval (a := a) (b := b)
  have hp1 := hp.sub (absolutelyContinuousOnInterval_const_real 1 a b)
  have hq1 := hq.add (absolutelyContinuousOnInterval_const_real 1 a b)
  have hd : ∀ᵐ t, t ∈ uIcc a b →
      HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t := by
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 hode] with t ht hmem
      using ht (uIcc_of_le hab ▸ hmem)
  rw [← intervalIntegral.integral_add (hu.mul_continuousOn Real.continuous_cos.continuousOn)
      (hv.mul_continuousOn Real.continuous_sin.continuousOn),
    ← intervalIntegral.integral_sub (hv.mul_continuousOn Real.continuous_cos.continuousOn)
      (hu.mul_continuousOn Real.continuous_sin.continuousOn)]
  refine ⟨ac_intervalIntegral_eq_sub_of_ae_hasDerivAt ((hp1.mul hc).add (hq1.mul hs))
    (hd.mono fun t ht hmem => ?_), ac_intervalIntegral_eq_sub_of_ae_hasDerivAt
      ((hp1.neg.mul hs).add (hq1.mul hc)) (hd.mono fun t ht hmem => ?_)⟩
  · exact ((((ht hmem).1.sub_const 1).mul (Real.hasDerivAt_cos t)).add
      (((ht hmem).2.add_const 1).mul (Real.hasDerivAt_sin t))).congr_deriv (by ring)
  · exact ((((ht hmem).1.sub_const 1).neg.mul (Real.hasDerivAt_sin t)).add
      (((ht hmem).2.add_const 1).mul (Real.hasDerivAt_cos t))).congr_deriv
        (by simp only [Pi.neg_apply]; ring)

theorem forwardSineConvolution_eq_moments
    {u : ℝ → ℝ} {a t : ℝ} (hu : IntervalIntegrable u volume a t) :
    forwardSineConvolution u a t =
      Real.sin t * (∫ s in a..t, u s * Real.cos s) -
        Real.cos t * (∫ s in a..t, u s * Real.sin s) := by
  rw [forwardSineConvolution, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      ((hu.mul_continuousOn Real.continuous_cos.continuousOn).const_mul _)
      ((hu.mul_continuousOn Real.continuous_sin.continuousOn).const_mul _)]
  congr 1 with s
  rw [Real.sin_sub]; ring

theorem forwardCosineConvolution_eq_moments
    {r : ℝ → ℝ} {a t : ℝ} (hr : IntervalIntegrable r volume a t) :
    forwardCosineConvolution r a t =
      Real.cos t * (∫ s in a..t, r s * Real.cos s) +
        Real.sin t * (∫ s in a..t, r s * Real.sin s) := by
  rw [forwardCosineConvolution, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
      ((hr.mul_continuousOn Real.continuous_cos.continuousOn).const_mul _)
      ((hr.mul_continuousOn Real.continuous_sin.continuousOn).const_mul _)]
  congr 1 with s
  rw [Real.cos_sub]; ring

theorem backwardCosineConvolution_eq_moments
    {r : ℝ → ℝ} {b t : ℝ} (hr : IntervalIntegrable r volume t b) :
    backwardCosineConvolution r b t =
      Real.cos t * (∫ s in t..b, r s * Real.cos s) +
        Real.sin t * (∫ s in t..b, r s * Real.sin s) := by
  rw [backwardCosineConvolution, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
      ((hr.mul_continuousOn Real.continuous_cos.continuousOn).const_mul _)
      ((hr.mul_continuousOn Real.continuous_sin.continuousOn).const_mul _)]
  congr 1 with s
  rw [Real.cos_sub]; ring

theorem secondMomentum_forward_convolution
    {p q u v : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hp : AbsolutelyContinuousOnInterval p 0 t)
    (hq : AbsolutelyContinuousOnInterval q 0 t)
    (hu : IntervalIntegrable u volume 0 t) (hv : IntervalIntegrable v volume 0 t)
    (hode : ∀ᵐ s ∂volume.restrict (Icc 0 t),
      HasDerivAt p (u s - 1 - q s) s ∧ HasDerivAt q (v s - 1 + p s) s) :
    q t + 1 = (p 0 - 1) * Real.sin t + (q 0 + 1) * Real.cos t +
      forwardSineConvolution u 0 t + forwardCosineConvolution v 0 t := by
  obtain ⟨hX, hY⟩ := momentum_rotation_integrals ht hp hq hu hv hode
  simp only [momentumRotX, momentumRotY, Real.cos_zero, Real.sin_zero] at hX hY
  rw [forwardSineConvolution_eq_moments hu, forwardCosineConvolution_eq_moments hv]
  linear_combination -Real.sin t * hX - Real.cos t * hY - (q t + 1) * Real.sin_sq_add_cos_sq t

theorem firstMomentum_backward_convolution
    {p q u v : ℝ → ℝ} {t : ℝ} (ht : t ≤ Real.pi / 2)
    (hp : AbsolutelyContinuousOnInterval p t (Real.pi / 2))
    (hq : AbsolutelyContinuousOnInterval q t (Real.pi / 2))
    (hu : IntervalIntegrable u volume t (Real.pi / 2))
    (hv : IntervalIntegrable v volume t (Real.pi / 2))
    (hode : ∀ᵐ s ∂volume.restrict (Icc t (Real.pi / 2)),
      HasDerivAt p (u s - 1 - q s) s ∧ HasDerivAt q (v s - 1 + p s) s) :
    1 - p t = (1 - p (Real.pi / 2)) * Real.sin t -
      (q (Real.pi / 2) + 1) * Real.cos t +
        backwardCosineConvolution u (Real.pi / 2) t +
          backwardSineConvolution v (Real.pi / 2) t := by
  obtain ⟨hX, hY⟩ := momentum_rotation_integrals ht hp hq hu hv hode
  simp only [momentumRotX, momentumRotY, Real.cos_pi_div_two, Real.sin_pi_div_two] at hX hY
  rw [backwardCosineConvolution_eq_moments hu, backwardSineConvolution_eq_moments hv]
  linear_combination -Real.cos t * hX + Real.sin t * hY + (p t - 1) * Real.sin_sq_add_cos_sq t

theorem absolutelyContinuousOnInterval_forwardSineConvolution
    {u : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hu : IntervalIntegrable u volume a b) :
    AbsolutelyContinuousOnInterval (forwardSineConvolution u a) a b := by
  have _ := hab -- not needed by the proof; it stays in the statement for the callers
  have hA := (hu.mul_continuousOn Real.continuous_cos.continuousOn)
    |>.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hB := (hu.mul_continuousOn Real.continuous_sin.continuousOn)
    |>.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  refine ((Real.contDiff_sin.contDiffOn.absolutelyContinuousOnInterval.mul hA).sub
    (Real.contDiff_cos.contDiffOn.absolutelyContinuousOnInterval.mul hB)).congr fun t ht => ?_
  exact (forwardSineConvolution_eq_moments (hu.mono_set (uIcc_subset_uIcc_left ht))).symm

theorem absolutelyContinuousOnInterval_forwardCosineConvolution
    {r : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hr : IntervalIntegrable r volume a b) :
    AbsolutelyContinuousOnInterval (forwardCosineConvolution r a) a b := by
  have _ := hab -- not needed by the proof; it stays in the statement for the callers
  have hA := (hr.mul_continuousOn Real.continuous_cos.continuousOn)
    |>.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hB := (hr.mul_continuousOn Real.continuous_sin.continuousOn)
    |>.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  refine ((Real.contDiff_cos.contDiffOn.absolutelyContinuousOnInterval.mul hA).add
    (Real.contDiff_sin.contDiffOn.absolutelyContinuousOnInterval.mul hB)).congr fun t ht => ?_
  exact (forwardCosineConvolution_eq_moments (hr.mono_set (uIcc_subset_uIcc_left ht))).symm

theorem absolutelyContinuousOnInterval_backwardCosineConvolution
    {r : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hr : IntervalIntegrable r volume a b) :
    AbsolutelyContinuousOnInterval (backwardCosineConvolution r b) a b := by
  have _ := hab -- not needed by the proof; it stays in the statement for the callers
  have hA := absolutelyContinuousOnInterval_integral_left
    (hr.mul_continuousOn Real.continuous_cos.continuousOn)
  have hB := absolutelyContinuousOnInterval_integral_left
    (hr.mul_continuousOn Real.continuous_sin.continuousOn)
  refine ((Real.contDiff_cos.contDiffOn.absolutelyContinuousOnInterval.mul hA).add
    (Real.contDiff_sin.contDiffOn.absolutelyContinuousOnInterval.mul hB)).congr fun t ht => ?_
  exact (backwardCosineConvolution_eq_moments (hr.mono_set (uIcc_subset_uIcc_right ht))).symm

theorem forwardCosineConvolution_add_complement
    {v : ℝ → ℝ} {t : ℝ} (hv : IntervalIntegrable v volume 0 t) :
    forwardCosineConvolution v 0 t +
      forwardCosineConvolution (fun s => 1 - v s) 0 t = Real.sin t := by
  have hc : Continuous (fun s : ℝ => Real.cos (t - s)) := by fun_prop
  rw [forwardCosineConvolution, forwardCosineConvolution, ← intervalIntegral.integral_add
    (hv.mul_continuousOn hc.continuousOn)
    ((intervalIntegrable_const.sub hv).mul_continuousOn hc.continuousOn)]
  simp [intervalIntegral.integral_comp_sub_left, ← add_mul]

theorem backwardCosineConvolution_add_complement
    {u : ℝ → ℝ} {t : ℝ} (hu : IntervalIntegrable u volume t (Real.pi / 2)) :
    backwardCosineConvolution u (Real.pi / 2) t +
      backwardCosineConvolution (fun s => 1 - u s) (Real.pi / 2) t = Real.cos t := by
  have hc : Continuous (fun s : ℝ => Real.cos (s - t)) := by fun_prop
  rw [backwardCosineConvolution, backwardCosineConvolution, ← intervalIntegral.integral_add
    (hu.mul_continuousOn hc.continuousOn)
    ((intervalIntegrable_const.sub hu).mul_continuousOn hc.continuousOn)]
  simp [intervalIntegral.integral_comp_sub_right, ← add_mul, Real.sin_pi_div_two_sub]

end AmbidextrousSofa.Analysis
