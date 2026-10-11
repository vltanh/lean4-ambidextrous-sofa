module

public import AmbidextrousSofa.Analysis.AdaptiveGlobalBoundary

@[expose] public section

/-!
# Horizontal translation of the adaptive functional

An actual horizontal translation adds `b cos` to the first support and
subtracts `b sin` from the companion support. Both affine momenta are
unchanged. The density change is an exact total derivative. Its boundary
term vanishes when the two vertical supports have the same value, in
particular for the unit-strip top traces. This also supplies the centered
common-width traces without imposing symmetry on the two functions.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa.Analysis

def QuarterPair.horizontalTranslate (u : QuarterPair) (b : ℝ) : QuarterPair where
  f := fun t => u.f t + b * Real.cos t
  g := fun t => u.g t - b * Real.sin t
  fD := fun t => u.fD t - b * Real.sin t
  gD := fun t => u.gD t - b * Real.cos t
  continuous_f := u.continuous_f.add (Real.continuous_cos.continuousOn.const_mul b)
  continuous_g := u.continuous_g.sub (Real.continuous_sin.continuousOn.const_mul b)
  continuous_fD := u.continuous_fD.sub (Real.continuous_sin.continuousOn.const_mul b)
  continuous_gD := u.continuous_gD.sub (Real.continuous_cos.continuousOn.const_mul b)
  hasDeriv_f := by
    intro t ht
    exact ((u.hasDeriv_f t ht).add
      ((Real.hasDerivAt_cos t).const_mul b).hasDerivWithinAt).congr_deriv (by ring)
  hasDeriv_g := fun t ht => (u.hasDeriv_g t ht).sub
    ((Real.hasDerivAt_sin t).const_mul b).hasDerivWithinAt

def horizontalTranslationDensity (u : QuarterPair) (t : ℝ) : ℝ :=
  (3 * (u.fD t * Real.sin t + u.f t * Real.cos t +
      u.gD t * Real.cos t - u.g t * Real.sin t) + Real.sin t - Real.cos t) / 2

/-- Exact boundary correction for arbitrary top traces. No contact-sign assumptions enter: both
momenta agree exactly before the positive and negative parts are taken. -/
theorem adaptiveFunctional_horizontalTranslate (u : QuarterPair) (b : ℝ) :
    adaptiveFunctional (u.horizontalTranslate b) = adaptiveFunctional u +
      (3 * b / 2) * (u.f (Real.pi / 2) - u.g 0) := by
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have := u.continuous_f; have := u.continuous_g; have := u.continuous_fD; have := u.continuous_gD
  have hD : IntervalIntegrable (horizontalTranslationDensity u) volume 0 (Real.pi / 2) :=
    ContinuousOn.intervalIntegrable_of_Icc hL (by unfold horizontalTranslationDensity; fun_prop)
  have hpq : ∀ t, adaptiveDensity (u.horizontalTranslate b) t =
      adaptiveDensity u t + b * horizontalTranslationDensity u t := fun t => by
    have hp : (u.horizontalTranslate b).p t = u.p t := by
      simp only [QuarterPair.p, QuarterPair.horizontalTranslate]; ring
    have hq : (u.horizontalTranslate b).q t = u.q t := by
      simp only [QuarterPair.q, QuarterPair.horizontalTranslate]; ring
    rw [adaptiveDensity, adaptiveDensity, hp, hq]
    simp only [QuarterPair.horizontalTranslate, horizontalTranslationDensity]
    ring
  simp only [adaptiveFunctional, hpq]
  rw [intervalIntegral.integral_add ((continuousOn_adaptiveDensity u).intervalIntegrable_of_Icc hL)
    (hD.const_mul b), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hL (f := fun t =>
      (3 * (u.f t * Real.sin t + u.g t * Real.cos t) - Real.cos t - Real.sin t) / 2)
      (by fun_prop) (fun t ht => ?_) hD]
  · simp
    ring
  have hs := (Real.hasDerivAt_sin t).hasDerivWithinAt (s := Ioi t)
  have hc := (Real.hasDerivAt_cos t).hasDerivWithinAt (s := Ioi t)
  exact (((((((u.hasDeriv_f t ht).mul hs).add ((u.hasDeriv_g t ht).mul hc)).const_mul 3).sub
    hc).sub hs).div_const 2).congr_deriv (by unfold horizontalTranslationDensity; ring)

theorem adaptiveFunctional_horizontalTranslate_of_topTraces (u : QuarterPair) (b : ℝ)
    (hfL : u.f (Real.pi / 2) = 1) (hg0 : u.g 0 = 1) :
    adaptiveFunctional (u.horizontalTranslate b) = adaptiveFunctional u := by
  simp [adaptiveFunctional_horizontalTranslate, hfL, hg0]

/-- Centering changes neither function's top trace and gives the common
half-width from the sum of the original two horizontal supports. -/
theorem QuarterPair.widthTraces_centered (u : QuarterPair)
    (hfL : u.f (Real.pi / 2) = 1) (hg0 : u.g 0 = 1) :
    (u.horizontalTranslate ((u.g (Real.pi / 2) - u.f 0) / 2)).WidthTraces
      ((u.f 0 + u.g (Real.pi / 2)) / 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [QuarterPair.horizontalTranslate, hfL, hg0] <;> ring

end AmbidextrousSofa.Analysis
