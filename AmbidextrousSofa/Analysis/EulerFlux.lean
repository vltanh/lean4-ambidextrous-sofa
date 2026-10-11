module

public import AmbidextrousSofa.Analysis.AdaptiveFunctional

@[expose] public section

/-!
# Euler flux and the first-variation boundary identity

The stationary condition is obtained from actual derivative equations by
the fundamental theorem of calculus. The same proof records the boundary
terms for variations that change the width.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa.Analysis

attribute [local fun_prop] QuarterPair.continuous_f QuarterPair.continuous_g
  QuarterPair.continuous_fD QuarterPair.continuous_gD

def QuarterPair.fluxF (u : QuarterPair) (t : ℝ) : ℝ :=
  -u.fD t - (u.g t - 1) / 2 - min (u.p t) 0

def QuarterPair.fluxG (u : QuarterPair) (t : ℝ) : ℝ :=
  -u.gD t + (u.f t - 1) / 2 - max (u.q t) 0

def QuarterPair.forceF (u : QuarterPair) (t : ℝ) : ℝ :=
  2 * u.f t - 1 + u.gD t / 2 - max (u.q t) 0

def QuarterPair.forceG (u : QuarterPair) (t : ℝ) : ℝ :=
  2 * u.g t - 1 - u.fD t / 2 + min (u.p t) 0

/-- The weak first variation follows from right derivative equations for
the continuous momenta. No second derivative of the profile is assumed. -/
theorem adaptiveFirstVariation_eq_boundary (u v : QuarterPair)
    (hf : ∀ t ∈ Ioo 0 (Real.pi / 2),
      HasDerivWithinAt u.fluxF (u.forceF t) (Ioi t) t)
    (hg : ∀ t ∈ Ioo 0 (Real.pi / 2),
      HasDerivWithinAt u.fluxG (u.forceG t) (Ioi t) t) :
    adaptiveFirstVariation u v =
      (u.fluxF (Real.pi / 2) * v.f (Real.pi / 2) +
        u.fluxG (Real.pi / 2) * v.g (Real.pi / 2)) -
      (u.fluxF 0 * v.f 0 + u.fluxG 0 * v.g 0) := by
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hL
    (by unfold QuarterPair.fluxF QuarterPair.fluxG QuarterPair.p QuarterPair.q; fun_prop)
    (fun t ht => (((hf t ht).mul (v.hasDeriv_f t ht)).add
      ((hg t ht).mul (v.hasDeriv_g t ht))).congr_deriv ?_)
    ((continuousOn_adaptiveLinearDensity u v).intervalIntegrable_of_Icc hL)
  unfold adaptiveLinearDensity QuarterPair.forceF QuarterPair.forceG QuarterPair.fluxF
    QuarterPair.fluxG
  ring

theorem QuarterPair.stationary_of_euler (u : QuarterPair)
    (hf : ∀ t ∈ Ioo 0 (Real.pi / 2),
      HasDerivWithinAt u.fluxF (u.forceF t) (Ioi t) t)
    (hg : ∀ t ∈ Ioo 0 (Real.pi / 2),
      HasDerivWithinAt u.fluxG (u.forceG t) (Ioi t) t) : u.Stationary := by
  rintro v ⟨hvf0, hvg0, hvfL, hvgL⟩
  rw [adaptiveFirstVariation_eq_boundary u v hf hg, hvf0, hvg0, hvfL, hvgL]
  ring

end AmbidextrousSofa.Analysis
