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

theorem QuarterPair.p_horizontalTranslate (u : QuarterPair) (b t : ℝ) :
    (u.horizontalTranslate b).p t = u.p t := by
  unfold QuarterPair.p QuarterPair.horizontalTranslate
  ring

theorem QuarterPair.q_horizontalTranslate (u : QuarterPair) (b t : ℝ) :
    (u.horizontalTranslate b).q t = u.q t := by
  unfold QuarterPair.q QuarterPair.horizontalTranslate
  ring

def horizontalTranslationDensity (u : QuarterPair) (t : ℝ) : ℝ :=
  (3 * (u.fD t * Real.sin t + u.f t * Real.cos t +
      u.gD t * Real.cos t - u.g t * Real.sin t) + Real.sin t - Real.cos t) / 2

def horizontalTranslationPrimitive (u : QuarterPair) (t : ℝ) : ℝ :=
  (3 * (u.f t * Real.sin t + u.g t * Real.cos t) - Real.cos t - Real.sin t) / 2

theorem continuousOn_horizontalTranslationDensity (u : QuarterPair) :
    ContinuousOn (horizontalTranslationDensity u) (Icc 0 (Real.pi / 2)) := by
  have hf := u.continuous_f
  have hg := u.continuous_g
  have hfD := u.continuous_fD
  have hgD := u.continuous_gD
  unfold horizontalTranslationDensity
  fun_prop

theorem continuousOn_horizontalTranslationPrimitive (u : QuarterPair) :
    ContinuousOn (horizontalTranslationPrimitive u) (Icc 0 (Real.pi / 2)) := by
  have hf := u.continuous_f
  have hg := u.continuous_g
  unfold horizontalTranslationPrimitive
  fun_prop

theorem hasDerivWithinAt_horizontalTranslationPrimitive (u : QuarterPair)
    {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    HasDerivWithinAt (horizontalTranslationPrimitive u) (horizontalTranslationDensity u t)
      (Ioi t) t := by
  have hs := (Real.hasDerivAt_sin t).hasDerivWithinAt (s := Ioi t)
  have hc := (Real.hasDerivAt_cos t).hasDerivWithinAt (s := Ioi t)
  have h := (((((u.hasDeriv_f t ht).mul hs).add
    ((u.hasDeriv_g t ht).mul hc)).const_mul 3).sub hc).sub hs
  exact (h.div_const 2).congr_deriv (by unfold horizontalTranslationDensity; ring)

/-- No contact-sign assumptions enter the translation identity: both
momenta agree exactly before the positive and negative parts are taken. -/
theorem adaptiveDensity_horizontalTranslate (u : QuarterPair) (b t : ℝ) :
    adaptiveDensity (u.horizontalTranslate b) t =
      adaptiveDensity u t + b * horizontalTranslationDensity u t := by
  unfold adaptiveDensity
  rw [QuarterPair.p_horizontalTranslate, QuarterPair.q_horizontalTranslate]
  unfold QuarterPair.horizontalTranslate horizontalTranslationDensity
  ring

theorem integral_horizontalTranslationDensity (u : QuarterPair) :
    (∫ t in (0 : ℝ)..(Real.pi / 2), horizontalTranslationDensity u t) =
      3 / 2 * (u.f (Real.pi / 2) - u.g 0) := by
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  calc
    (∫ t in (0 : ℝ)..(Real.pi / 2), horizontalTranslationDensity u t) =
        horizontalTranslationPrimitive u (Real.pi / 2) - horizontalTranslationPrimitive u 0 :=
      intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hL
        (continuousOn_horizontalTranslationPrimitive u)
        (fun t ht => hasDerivWithinAt_horizontalTranslationPrimitive u ht)
        (ContinuousOn.intervalIntegrable_of_Icc hL (continuousOn_horizontalTranslationDensity u))
    _ = 3 / 2 * (u.f (Real.pi / 2) - u.g 0) := by
      simp only [horizontalTranslationPrimitive, Real.sin_zero, Real.cos_zero,
        Real.sin_pi_div_two, Real.cos_pi_div_two, mul_zero, mul_one, add_zero, zero_add]
      ring

/-- Exact boundary correction for arbitrary top traces. -/
theorem adaptiveFunctional_horizontalTranslate (u : QuarterPair) (b : ℝ) :
    adaptiveFunctional (u.horizontalTranslate b) = adaptiveFunctional u +
      (3 * b / 2) * (u.f (Real.pi / 2) - u.g 0) := by
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hu := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hL
    (continuousOn_adaptiveDensity u)
  have hd := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hL
    (continuousOn_horizontalTranslationDensity u)
  calc
    adaptiveFunctional (u.horizontalTranslate b) =
        ∫ t in (0 : ℝ)..(Real.pi / 2), adaptiveDensity u t + b * horizontalTranslationDensity u t := by
      unfold adaptiveFunctional
      apply intervalIntegral.integral_congr
      intro t _
      exact adaptiveDensity_horizontalTranslate u b t
    _ = adaptiveFunctional u + b *
        ∫ t in (0 : ℝ)..(Real.pi / 2), horizontalTranslationDensity u t := by
      rw [intervalIntegral.integral_add hu (hd.const_mul b), intervalIntegral.integral_const_mul]
      rfl
    _ = adaptiveFunctional u + (3 * b / 2) * (u.f (Real.pi / 2) - u.g 0) := by
      rw [integral_horizontalTranslationDensity]
      ring

theorem adaptiveFunctional_horizontalTranslate_of_equal_top_traces (u : QuarterPair) (b : ℝ)
    (htrace : u.f (Real.pi / 2) = u.g 0) :
    adaptiveFunctional (u.horizontalTranslate b) = adaptiveFunctional u := by
  rw [adaptiveFunctional_horizontalTranslate, htrace, sub_self, mul_zero, add_zero]

theorem adaptiveFunctional_horizontalTranslate_of_topTraces (u : QuarterPair) (b : ℝ)
    (hfL : u.f (Real.pi / 2) = 1) (hg0 : u.g 0 = 1) :
    adaptiveFunctional (u.horizontalTranslate b) = adaptiveFunctional u :=
  adaptiveFunctional_horizontalTranslate_of_equal_top_traces u b (hfL.trans hg0.symm)

/-- Centering changes neither function's top trace and gives the common
half-width from the sum of the original two horizontal supports. -/
theorem QuarterPair.widthTraces_centered (u : QuarterPair)
    (hfL : u.f (Real.pi / 2) = 1) (hg0 : u.g 0 = 1) :
    (u.horizontalTranslate ((u.g (Real.pi / 2) - u.f 0) / 2)).WidthTraces
      ((u.f 0 + u.g (Real.pi / 2)) / 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [QuarterPair.horizontalTranslate, Real.cos_zero, Real.sin_zero,
      Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, mul_one,
      add_zero, sub_zero, hfL, hg0] <;> ring

end AmbidextrousSofa.Analysis
