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
  calc
    _ = ∫ t in a..b, deriv E t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hD] with t ht hmem
      exact (ht (Ioc_subset_Icc_self hmem)).deriv.symm
    _ = E b - E a := hE.integral_deriv_eq_sub

theorem momentum_rotation_integrals
    {p q u v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hp : AbsolutelyContinuousOnInterval p a b)
    (hq : AbsolutelyContinuousOnInterval q a b)
    (hode : ∀ᵐ t ∂volume.restrict (Icc a b),
      HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t) :
    (∫ t in a..b, u t * Real.cos t + v t * Real.sin t) =
      momentumRotX p q b - momentumRotX p q a ∧
    (∫ t in a..b, -u t * Real.sin t + v t * Real.cos t) =
      momentumRotY p q b - momentumRotY p q a := by
  have hc : AbsolutelyContinuousOnInterval Real.cos a b :=
    (show ContDiff ℝ 1 Real.cos by fun_prop).contDiffOn.absolutelyContinuousOnInterval
  have hs : AbsolutelyContinuousOnInterval Real.sin a b :=
    (show ContDiff ℝ 1 Real.sin by fun_prop).contDiffOn.absolutelyContinuousOnInterval
  have hp1 := hp.sub (absolutelyContinuousOnInterval_const_real 1 a b)
  have hq1 := hq.add (absolutelyContinuousOnInterval_const_real 1 a b)
  have hX : AbsolutelyContinuousOnInterval (momentumRotX p q) a b :=
    (hp1.mul hc).add (hq1.mul hs)
  have hY : AbsolutelyContinuousOnInterval (momentumRotY p q) a b :=
    (hp1.neg.mul hs).add (hq1.mul hc)
  have hode' := (ae_restrict_iff' measurableSet_Icc).1 hode
  constructor
  · apply ac_intervalIntegral_eq_sub_of_ae_hasDerivAt hX
    filter_upwards [hode'] with t ht hmem
    have hm : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using hmem
    have hd := (((ht hm).1.sub_const 1).mul (Real.hasDerivAt_cos t)).add
      (((ht hm).2.add_const 1).mul (Real.hasDerivAt_sin t))
    exact hd.congr_deriv (by ring)
  · apply ac_intervalIntegral_eq_sub_of_ae_hasDerivAt hY
    filter_upwards [hode'] with t ht hmem
    have hm : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using hmem
    have hd := ((((ht hm).1.sub_const 1).neg).mul (Real.hasDerivAt_sin t)).add
      (((ht hm).2.add_const 1).mul (Real.hasDerivAt_cos t))
    exact hd.congr_deriv (by ring)

theorem momentum_rotation_inverse (p q : ℝ → ℝ) (t : ℝ) :
    momentumRotX p q t * Real.cos t - momentumRotY p q t * Real.sin t = p t - 1 ∧
      momentumRotX p q t * Real.sin t + momentumRotY p q t * Real.cos t = q t + 1 := by
  have hp := congrArg (fun x : ℝ => (p t - 1) * x) (Real.sin_sq_add_cos_sq t)
  have hq := congrArg (fun x : ℝ => (q t + 1) * x) (Real.sin_sq_add_cos_sq t)
  unfold momentumRotX momentumRotY
  constructor <;> nlinarith

theorem forwardSineConvolution_eq_moments
    {u : ℝ → ℝ} {a t : ℝ} (hu : IntervalIntegrable u volume a t) :
    forwardSineConvolution u a t =
      Real.sin t * (∫ s in a..t, u s * Real.cos s) -
        Real.cos t * (∫ s in a..t, u s * Real.sin s) := by
  have hsin := hu.mul_continuousOn Real.continuous_sin.continuousOn
  have hcos := hu.mul_continuousOn Real.continuous_cos.continuousOn
  unfold forwardSineConvolution
  calc
    _ = ∫ s in a..t,
        Real.sin t * (u s * Real.cos s) - Real.cos t * (u s * Real.sin s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Real.sin_sub]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub (hcos.const_mul _) (hsin.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem forwardCosineConvolution_eq_moments
    {r : ℝ → ℝ} {a t : ℝ} (hr : IntervalIntegrable r volume a t) :
    forwardCosineConvolution r a t =
      Real.cos t * (∫ s in a..t, r s * Real.cos s) +
        Real.sin t * (∫ s in a..t, r s * Real.sin s) := by
  have hsin := hr.mul_continuousOn Real.continuous_sin.continuousOn
  have hcos := hr.mul_continuousOn Real.continuous_cos.continuousOn
  unfold forwardCosineConvolution
  calc
    _ = ∫ s in a..t,
        Real.cos t * (r s * Real.cos s) + Real.sin t * (r s * Real.sin s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Real.cos_sub]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hcos.const_mul _) (hsin.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem backwardCosineConvolution_eq_moments
    {r : ℝ → ℝ} {b t : ℝ} (hr : IntervalIntegrable r volume t b) :
    backwardCosineConvolution r b t =
      Real.cos t * (∫ s in t..b, r s * Real.cos s) +
        Real.sin t * (∫ s in t..b, r s * Real.sin s) := by
  have hsin := hr.mul_continuousOn Real.continuous_sin.continuousOn
  have hcos := hr.mul_continuousOn Real.continuous_cos.continuousOn
  unfold backwardCosineConvolution
  calc
    _ = ∫ s in t..b,
        Real.cos t * (r s * Real.cos s) + Real.sin t * (r s * Real.sin s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Real.cos_sub]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hcos.const_mul _) (hsin.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem secondMomentum_forward_convolution
    {p q u v : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hp : AbsolutelyContinuousOnInterval p 0 t)
    (hq : AbsolutelyContinuousOnInterval q 0 t)
    (hu : IntervalIntegrable u volume 0 t) (hv : IntervalIntegrable v volume 0 t)
    (hode : ∀ᵐ s ∂volume.restrict (Icc 0 t),
      HasDerivAt p (u s - 1 - q s) s ∧ HasDerivAt q (v s - 1 + p s) s) :
    q t + 1 = (p 0 - 1) * Real.sin t + (q 0 + 1) * Real.cos t +
      forwardSineConvolution u 0 t + forwardCosineConvolution v 0 t := by
  obtain ⟨hX, hY⟩ := momentum_rotation_integrals ht hp hq hode
  have huc := hu.mul_continuousOn Real.continuous_cos.continuousOn
  have hus := hu.mul_continuousOn Real.continuous_sin.continuousOn
  have hvc := hv.mul_continuousOn Real.continuous_cos.continuousOn
  have hvs := hv.mul_continuousOn Real.continuous_sin.continuousOn
  rw [intervalIntegral.integral_add huc hvs] at hX
  rw [show (fun s => -u s * Real.sin s + v s * Real.cos s) =
      (fun s => -(u s * Real.sin s) + v s * Real.cos s) by funext s; ring,
    intervalIntegral.integral_add hus.neg hvc, intervalIntegral.integral_neg] at hY
  have hXm := congrArg (fun x : ℝ => x * Real.sin t) hX
  have hYm := congrArg (fun x : ℝ => x * Real.cos t) hY
  have hi := (momentum_rotation_inverse p q t).2
  have hX0 : momentumRotX p q 0 = p 0 - 1 := by simp [momentumRotX]
  have hY0 : momentumRotY p q 0 = q 0 + 1 := by simp [momentumRotY]
  rw [hX0] at hXm
  rw [hY0] at hYm
  rw [forwardSineConvolution_eq_moments hu, forwardCosineConvolution_eq_moments hv]
  nlinarith

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
  obtain ⟨hX, hY⟩ := momentum_rotation_integrals ht hp hq hode
  have huc := hu.mul_continuousOn Real.continuous_cos.continuousOn
  have hus := hu.mul_continuousOn Real.continuous_sin.continuousOn
  have hvc := hv.mul_continuousOn Real.continuous_cos.continuousOn
  have hvs := hv.mul_continuousOn Real.continuous_sin.continuousOn
  rw [intervalIntegral.integral_add huc hvs] at hX
  rw [show (fun s => -u s * Real.sin s + v s * Real.cos s) =
      (fun s => -(u s * Real.sin s) + v s * Real.cos s) by funext s; ring,
    intervalIntegral.integral_add hus.neg hvc, intervalIntegral.integral_neg] at hY
  have hXm := congrArg (fun x : ℝ => x * Real.cos t) hX
  have hYm := congrArg (fun x : ℝ => x * Real.sin t) hY
  have hi := (momentum_rotation_inverse p q t).1
  have hXL : momentumRotX p q (Real.pi / 2) = q (Real.pi / 2) + 1 := by simp [momentumRotX]
  have hYL : momentumRotY p q (Real.pi / 2) = 1 - p (Real.pi / 2) := by simp [momentumRotY]
  rw [hXL] at hXm
  rw [hYL] at hYm
  rw [backwardCosineConvolution_eq_moments hu, backwardSineConvolution_eq_moments hv]
  nlinarith

theorem absolutelyContinuousOnInterval_forwardSineConvolution
    {u : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hu : IntervalIntegrable u volume a b) :
    AbsolutelyContinuousOnInterval (forwardSineConvolution u a) a b := by
  have hsin := hu.mul_continuousOn Real.continuous_sin.continuousOn
  have hcos := hu.mul_continuousOn Real.continuous_cos.continuousOn
  have hc : AbsolutelyContinuousOnInterval Real.cos a b :=
    (show ContDiff ℝ 1 Real.cos by fun_prop).contDiffOn.absolutelyContinuousOnInterval
  have hs : AbsolutelyContinuousOnInterval Real.sin a b :=
    (show ContDiff ℝ 1 Real.sin by fun_prop).contDiffOn.absolutelyContinuousOnInterval
  have hA := hcos.absolutelyContinuousOnInterval_intervalIntegral (show a ∈ uIcc a b by simp)
  have hB := hsin.absolutelyContinuousOnInterval_intervalIntegral (show a ∈ uIcc a b by simp)
  apply ((hs.mul hA).sub (hc.mul hB)).congr
  intro t ht
  have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
  have hut := hu.mono_set (show uIcc a t ⊆ uIcc a b by
    simpa only [uIcc_of_le ht'.1, uIcc_of_le hab] using
      (Icc_subset_Icc (le_refl a) ht'.2))
  exact (forwardSineConvolution_eq_moments hut).symm

theorem absolutelyContinuousOnInterval_forwardCosineConvolution
    {r : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hr : IntervalIntegrable r volume a b) :
    AbsolutelyContinuousOnInterval (forwardCosineConvolution r a) a b := by
  have hsin := hr.mul_continuousOn Real.continuous_sin.continuousOn
  have hcos := hr.mul_continuousOn Real.continuous_cos.continuousOn
  have hc : AbsolutelyContinuousOnInterval Real.cos a b :=
    (show ContDiff ℝ 1 Real.cos by fun_prop).contDiffOn.absolutelyContinuousOnInterval
  have hs : AbsolutelyContinuousOnInterval Real.sin a b :=
    (show ContDiff ℝ 1 Real.sin by fun_prop).contDiffOn.absolutelyContinuousOnInterval
  have hA := hcos.absolutelyContinuousOnInterval_intervalIntegral (show a ∈ uIcc a b by simp)
  have hB := hsin.absolutelyContinuousOnInterval_intervalIntegral (show a ∈ uIcc a b by simp)
  apply ((hc.mul hA).add (hs.mul hB)).congr
  intro t ht
  have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
  have hrt := hr.mono_set (show uIcc a t ⊆ uIcc a b by
    simpa only [uIcc_of_le ht'.1, uIcc_of_le hab] using
      (Icc_subset_Icc (le_refl a) ht'.2))
  exact (forwardCosineConvolution_eq_moments hrt).symm

theorem absolutelyContinuousOnInterval_backwardCosineConvolution
    {r : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hr : IntervalIntegrable r volume a b) :
    AbsolutelyContinuousOnInterval (backwardCosineConvolution r b) a b := by
  have hsin := hr.mul_continuousOn Real.continuous_sin.continuousOn
  have hcos := hr.mul_continuousOn Real.continuous_cos.continuousOn
  have hc : AbsolutelyContinuousOnInterval Real.cos a b :=
    (show ContDiff ℝ 1 Real.cos by fun_prop).contDiffOn.absolutelyContinuousOnInterval
  have hs : AbsolutelyContinuousOnInterval Real.sin a b :=
    (show ContDiff ℝ 1 Real.sin by fun_prop).contDiffOn.absolutelyContinuousOnInterval
  have hA := absolutelyContinuousOnInterval_integral_left hcos
  have hB := absolutelyContinuousOnInterval_integral_left hsin
  apply ((hc.mul hA).add (hs.mul hB)).congr
  intro t ht
  have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
  have hrt := hr.mono_set (show uIcc t b ⊆ uIcc a b by
    simpa only [uIcc_of_le ht'.2, uIcc_of_le hab] using
      (Icc_subset_Icc ht'.1 (le_refl b)))
  exact (backwardCosineConvolution_eq_moments hrt).symm

theorem forwardCosineConvolution_add_complement
    {v : ℝ → ℝ} {t : ℝ} (hv : IntervalIntegrable v volume 0 t) :
    forwardCosineConvolution v 0 t +
      forwardCosineConvolution (fun s => 1 - v s) 0 t = Real.sin t := by
  have hc : Continuous (fun s : ℝ => Real.cos (t - s)) := by fun_prop
  have hvc := hv.mul_continuousOn hc.continuousOn
  have hrc := ((intervalIntegrable_const (c := (1 : ℝ))).sub hv).mul_continuousOn hc.continuousOn
  unfold forwardCosineConvolution
  rw [← intervalIntegral.integral_add hvc hrc]
  calc
    _ = ∫ s in 0..t, Real.cos (t - s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      ring
    _ = Real.sin t := by
      rw [intervalIntegral.integral_comp_sub_left, integral_cos]
      simp

theorem backwardCosineConvolution_add_complement
    {u : ℝ → ℝ} {t : ℝ} (hu : IntervalIntegrable u volume t (Real.pi / 2)) :
    backwardCosineConvolution u (Real.pi / 2) t +
      backwardCosineConvolution (fun s => 1 - u s) (Real.pi / 2) t = Real.cos t := by
  have hc : Continuous (fun s : ℝ => Real.cos (s - t)) := by fun_prop
  have huc := hu.mul_continuousOn hc.continuousOn
  have hrc := ((intervalIntegrable_const (c := (1 : ℝ))).sub hu).mul_continuousOn hc.continuousOn
  unfold backwardCosineConvolution
  rw [← intervalIntegral.integral_add huc hrc]
  calc
    _ = ∫ s in t..(Real.pi / 2), Real.cos (s - t) := by
      apply intervalIntegral.integral_congr
      intro s hs
      ring
    _ = Real.cos t := by
      rw [intervalIntegral.integral_comp_sub_right, integral_cos]
      simp only [sub_self, Real.sin_zero, sub_zero, Real.sin_pi_div_two_sub]

end AmbidextrousSofa.Analysis
