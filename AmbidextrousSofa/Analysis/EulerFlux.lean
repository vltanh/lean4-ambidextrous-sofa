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

def QuarterPair.fluxF (u : QuarterPair) (t : ℝ) : ℝ :=
  -u.fD t - (u.g t - 1) / 2 - min (u.p t) 0

def QuarterPair.fluxG (u : QuarterPair) (t : ℝ) : ℝ :=
  -u.gD t + (u.f t - 1) / 2 - max (u.q t) 0

def QuarterPair.forceF (u : QuarterPair) (t : ℝ) : ℝ :=
  2 * u.f t - 1 + u.gD t / 2 - max (u.q t) 0

def QuarterPair.forceG (u : QuarterPair) (t : ℝ) : ℝ :=
  2 * u.g t - 1 - u.fD t / 2 + min (u.p t) 0

theorem QuarterPair.continuous_fluxF (u : QuarterPair) :
    ContinuousOn u.fluxF (Icc 0 (Real.pi / 2)) := by
  have hg := u.continuous_g
  have hfD := u.continuous_fD
  unfold QuarterPair.fluxF QuarterPair.p
  fun_prop

theorem QuarterPair.continuous_fluxG (u : QuarterPair) :
    ContinuousOn u.fluxG (Icc 0 (Real.pi / 2)) := by
  have hf := u.continuous_f
  have hgD := u.continuous_gD
  unfold QuarterPair.fluxG QuarterPair.q
  fun_prop

theorem QuarterPair.continuous_forceF (u : QuarterPair) :
    ContinuousOn u.forceF (Icc 0 (Real.pi / 2)) := by
  have hf := u.continuous_f
  have hgD := u.continuous_gD
  unfold QuarterPair.forceF QuarterPair.q
  fun_prop

theorem QuarterPair.continuous_forceG (u : QuarterPair) :
    ContinuousOn u.forceG (Icc 0 (Real.pi / 2)) := by
  have hg := u.continuous_g
  have hfD := u.continuous_fD
  unfold QuarterPair.forceG QuarterPair.p
  fun_prop

theorem adaptiveLinearDensity_eq_flux (u v : QuarterPair) (t : ℝ) :
    adaptiveLinearDensity u v t =
      u.forceF t * v.f t + u.fluxF t * v.fD t +
        (u.forceG t * v.g t + u.fluxG t * v.gD t) := by
  unfold adaptiveLinearDensity QuarterPair.forceF QuarterPair.forceG
    QuarterPair.fluxF QuarterPair.fluxG
  ring

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
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hL
    ((u.continuous_fluxF.mul v.continuous_f).add
      (u.continuous_fluxG.mul v.continuous_g))
  · intro t ht
    have h := ((hf t ht).mul (v.hasDeriv_f t ht)).add
      ((hg t ht).mul (v.hasDeriv_g t ht))
    exact h.congr_deriv (by rw [adaptiveLinearDensity_eq_flux]; ring)
  · exact ContinuousOn.intervalIntegrable_of_Icc hL (continuousOn_adaptiveLinearDensity u v)

theorem QuarterPair.stationary_of_euler (u : QuarterPair)
    (hf : ∀ t ∈ Ioo 0 (Real.pi / 2),
      HasDerivWithinAt u.fluxF (u.forceF t) (Ioi t) t)
    (hg : ∀ t ∈ Ioo 0 (Real.pi / 2),
      HasDerivWithinAt u.fluxG (u.forceG t) (Ioi t) t) : u.Stationary := by
  intro v hv
  rcases hv with ⟨hvf0, hvg0, hvfL, hvgL⟩
  rw [adaptiveFirstVariation_eq_boundary u v hf hg, hvf0, hvg0, hvfL, hvgL]
  ring

end AmbidextrousSofa.Analysis
