module

public import AmbidextrousSofa.Analysis.TiltedFirstUnitMoments

@[expose] public section

/-!
# Harmonic reconstruction from the actual momentum ODE

The rotating coordinates remove the homogeneous quarter-turn dynamics.
Their absolutely continuous fundamental theorem reconstructs each end of
an interval from the other one by the literal sine and cosine
convolutions used in the first-floor energy identities.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa.Analysis

def forwardCosineConvolution (r : ℝ → ℝ) (a t : ℝ) : ℝ :=
  ∫ s in a..t, r s * Real.cos (t - s)

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

theorem continuousOn_forwardCosineConvolution {r : ℝ → ℝ} {a b c : ℝ}
    (hr : IntervalIntegrable r volume a b) (hc : c ∈ uIcc a b) :
    ContinuousOn (forwardCosineConvolution r c) (uIcc a b) :=
  ((Real.continuous_cos.continuousOn.mul (intervalIntegral.continuousOn_primitive_interval'
    (hr.mul_continuousOn Real.continuous_cos.continuousOn) hc)).add
    (Real.continuous_sin.continuousOn.mul (intervalIntegral.continuousOn_primitive_interval'
      (hr.mul_continuousOn Real.continuous_sin.continuousOn) hc))).congr fun _ ht =>
    forwardCosineConvolution_eq_moments (hr.mono_set (uIcc_subset_uIcc hc ht))

/-- In rotating coordinates the homogeneous quarter-turn dynamics disappear, so each end of an
interval is reconstructed from the other one by sine and cosine convolutions based there. -/
theorem momentum_reconstruction
    {p q u v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hp : AbsolutelyContinuousOnInterval p a b)
    (hq : AbsolutelyContinuousOnInterval q a b)
    (hu : IntervalIntegrable u volume a b) (hv : IntervalIntegrable v volume a b)
    (hode : ∀ᵐ t ∂volume.restrict (Icc a b),
      HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t) :
    q b + 1 = (p a - 1) * Real.sin (b - a) + (q a + 1) * Real.cos (b - a) +
        forwardSineConvolution u a b + forwardCosineConvolution v a b ∧
      p a - 1 = (p b - 1) * Real.cos (b - a) + (q b + 1) * Real.sin (b - a) +
        forwardCosineConvolution u b a - forwardSineConvolution v b a := by
  obtain ⟨hX, hY⟩ : (∫ t in a..b, u t * Real.cos t) + (∫ t in a..b, v t * Real.sin t) =
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
  simp only [momentumRotX, momentumRotY] at hX hY
  rw [forwardSineConvolution_eq_moments hu, forwardCosineConvolution_eq_moments hv,
    forwardCosineConvolution_eq_moments hu.symm, forwardSineConvolution_eq_moments hv.symm,
    Real.sin_sub, Real.cos_sub]
  simp only [intervalIntegral.integral_symm a b]
  exact ⟨by linear_combination -Real.sin b * hX - Real.cos b * hY -
      (q b + 1) * Real.sin_sq_add_cos_sq b,
    by linear_combination Real.cos a * hX - Real.sin a * hY - (p a - 1) * Real.sin_sq_add_cos_sq a⟩

/-- The cosine convolutions of a density and of its complement add up to that of the constant
one. -/
theorem forwardCosineConvolution_add_complement {v : ℝ → ℝ} {c t : ℝ}
    (hv : IntervalIntegrable v volume c t) :
    forwardCosineConvolution v c t +
      forwardCosineConvolution (fun s => 1 - v s) c t = Real.sin (t - c) := by
  have hc : Continuous (fun s : ℝ => Real.cos (t - s)) := by fun_prop
  rw [forwardCosineConvolution, forwardCosineConvolution, ← intervalIntegral.integral_add
    (hv.mul_continuousOn hc.continuousOn)
    ((intervalIntegrable_const.sub hv).mul_continuousOn hc.continuousOn)]
  simp [intervalIntegral.integral_comp_sub_left, ← add_mul]

end AmbidextrousSofa.Analysis
