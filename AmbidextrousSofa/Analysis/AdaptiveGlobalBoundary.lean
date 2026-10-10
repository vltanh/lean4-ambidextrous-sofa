module

public import AmbidextrousSofa.Analysis.EulerFlux

@[expose] public section

/-!
# Width variations for the adaptive functional

This file proves the actual natural boundary condition for a local maximum
when the common horizontal endpoint is allowed to vary. The proof uses the
exact Taylor identity and a quadratic bound for both contact remainders;
it does not presume differentiability of an optimized value function.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace AmbidextrousSofa.Analysis

def QuarterPair.WidthTraces (u : QuarterPair) (a : ℝ) : Prop :=
  u.f 0 = a ∧ u.g 0 = 1 ∧ u.f (Real.pi / 2) = 1 ∧ u.g (Real.pi / 2) = a

def QuarterPair.addScaled (u : QuarterPair) (r : ℝ) (v : QuarterPair) : QuarterPair where
  f := fun t => u.f t + r * v.f t
  g := fun t => u.g t + r * v.g t
  fD := fun t => u.fD t + r * v.fD t
  gD := fun t => u.gD t + r * v.gD t
  continuous_f := u.continuous_f.add (v.continuous_f.const_mul r)
  continuous_g := u.continuous_g.add (v.continuous_g.const_mul r)
  continuous_fD := u.continuous_fD.add (v.continuous_fD.const_mul r)
  continuous_gD := u.continuous_gD.add (v.continuous_gD.const_mul r)
  hasDeriv_f := fun t ht => (u.hasDeriv_f t ht).add ((v.hasDeriv_f t ht).const_mul r)
  hasDeriv_g := fun t ht => (u.hasDeriv_g t ht).add ((v.hasDeriv_g t ht).const_mul r)

theorem negativeSquareBregman_le_square (x y : ℝ) :
    negativeSquareBregman x y ≤ (y - x) ^ 2 := by
  rcases le_total x 0 with hx | hx <;> rcases le_total y 0 with hy | hy
  · simp only [negativeSquareBregman, min_eq_left hx, min_eq_left hy]
    nlinarith
  · simp only [negativeSquareBregman, min_eq_left hx, min_eq_right hy]
    nlinarith [sq_nonneg y]
  · simp only [negativeSquareBregman, min_eq_right hx, min_eq_left hy]
    nlinarith [sq_nonneg x, mul_nonpos_of_nonneg_of_nonpos hx hy]
  · simp only [negativeSquareBregman, min_eq_right hx, min_eq_right hy]
    nlinarith [sq_nonneg (y - x)]

theorem positiveSquareBregman_le_square (x y : ℝ) :
    positiveSquareBregman x y ≤ (y - x) ^ 2 := by
  rcases le_total x 0 with hx | hx <;> rcases le_total y 0 with hy | hy
  · simp only [positiveSquareBregman, max_eq_right hx, max_eq_right hy]
    nlinarith [sq_nonneg (y - x)]
  · simp only [positiveSquareBregman, max_eq_right hx, max_eq_left hy]
    nlinarith [sq_nonneg x, mul_nonpos_of_nonpos_of_nonneg hx hy]
  · simp only [positiveSquareBregman, max_eq_left hx, max_eq_right hy]
    nlinarith [sq_nonneg y]
  · simp only [positiveSquareBregman, max_eq_left hx, max_eq_left hy]
    nlinarith

def variationContactDensity (v : QuarterPair) (t : ℝ) : ℝ :=
  ((v.fD t - v.g t) ^ 2 + (v.gD t + v.f t) ^ 2) / 2

def variationContactIntegral (v : QuarterPair) : ℝ :=
  ∫ t in (0 : ℝ)..(Real.pi / 2), variationContactDensity v t

theorem continuousOn_variationContactDensity (v : QuarterPair) :
    ContinuousOn (variationContactDensity v) (Icc 0 (Real.pi / 2)) := by
  exact (((v.continuous_fD.sub v.continuous_g).pow 2).add
    ((v.continuous_gD.add v.continuous_f).pow 2)).div_const 2

theorem contactDefectDensity_addScaled_le (u v : QuarterPair) (r t : ℝ) :
    contactDefectDensity u (u.addScaled r v) t ≤ r ^ 2 * variationContactDensity v t := by
  have hp := negativeSquareBregman_le_square (u.p t) ((u.addScaled r v).p t)
  have hq := positiveSquareBregman_le_square (u.q t) ((u.addScaled r v).q t)
  have hpdiff : ((u.addScaled r v).p t - u.p t) ^ 2 =
      r ^ 2 * (v.fD t - v.g t) ^ 2 := by
    unfold QuarterPair.p QuarterPair.addScaled
    ring
  have hqdiff : ((u.addScaled r v).q t - u.q t) ^ 2 =
      r ^ 2 * (v.gD t + v.f t) ^ 2 := by
    unfold QuarterPair.q QuarterPair.addScaled
    ring
  rw [hpdiff] at hp
  rw [hqdiff] at hq
  unfold contactDefectDensity variationContactDensity
  nlinarith

theorem adaptiveFirstVariation_addScaled_sub (u v : QuarterPair) (r : ℝ) :
    adaptiveFirstVariation u ((u.addScaled r v).sub u) = r * adaptiveFirstVariation u v := by
  unfold adaptiveFirstVariation
  calc
    _ = ∫ t in (0 : ℝ)..(Real.pi / 2), r * adaptiveLinearDensity u v t := by
      apply intervalIntegral.integral_congr
      intro t _
      unfold adaptiveLinearDensity QuarterPair.sub QuarterPair.addScaled
      ring
    _ = _ := intervalIntegral.integral_const_mul r _

theorem quadraticEnergy_addScaled_sub (u v : QuarterPair) (r : ℝ) :
    quadraticEnergy ((u.addScaled r v).sub u) = r ^ 2 * quadraticEnergy v := by
  rw [quadraticEnergy_eq_integral_density, quadraticEnergy_eq_integral_density]
  calc
    _ = ∫ t in (0 : ℝ)..(Real.pi / 2), r ^ 2 * quadraticDensity v t := by
      apply intervalIntegral.integral_congr
      intro t _
      unfold quadraticDensity QuarterPair.sub QuarterPair.addScaled
      ring
    _ = _ := intervalIntegral.integral_const_mul (r ^ 2) _

/-- An exact first-order term with a uniform quadratic lower error. This
controls the remainder needed for the natural boundary equation. -/
theorem adaptiveFunctional_addScaled_lower (u v : QuarterPair) (r : ℝ) :
    adaptiveFunctional u + r * adaptiveFirstVariation u v -
      r ^ 2 * (quadraticEnergy v + variationContactIntegral v) ≤
        adaptiveFunctional (u.addScaled r v) := by
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hc := ContinuousOn.intervalIntegrable_of_Icc hL
    (continuousOn_contactDefectDensity u (u.addScaled r v))
  have hv := ContinuousOn.intervalIntegrable_of_Icc hL (continuousOn_variationContactDensity v)
  have hbound := intervalIntegral.integral_mono_on hL hc (hv.const_mul (r ^ 2))
    (fun t _ => contactDefectDensity_addScaled_le u v r t)
  rw [intervalIntegral.integral_const_mul] at hbound
  rw [adaptiveFunctional_taylor u (u.addScaled r v),
    adaptiveFirstVariation_addScaled_sub, quadraticEnergy_addScaled_sub]
  change _ ≤ r ^ 2 * variationContactIntegral v at hbound
  nlinarith

/-- A local maximum of the penalized value forces the actual variation
to equal the prescribed linear endpoint cost. No envelope theorem is used. -/
theorem adaptiveFirstVariation_eq_of_local_max_addScaled
    (u v : QuarterPair) {c ε : ℝ} (hε : 0 < ε)
    (hmax : ∀ r ∈ Ioo (-ε) ε,
      adaptiveFunctional (u.addScaled r v) - r * c ≤ adaptiveFunctional u) :
    adaptiveFirstVariation u v = c := by
  let B := quadraticEnergy v + variationContactIntegral v
  let d := adaptiveFirstVariation u v - c
  have hlocal : IsLocalMax (fun r : ℝ => r * d - r ^ 2 * B) 0 := by
    change ∀ᶠ r in 𝓝 (0 : ℝ), r * d - r ^ 2 * B ≤ 0 * d - 0 ^ 2 * B
    filter_upwards [Ioo_mem_nhds (by linarith : -ε < 0) hε] with r hr
    have hlow := adaptiveFunctional_addScaled_lower u v r
    have hupp := hmax r hr
    dsimp [B, d]
    nlinarith
  have hderiv : HasDerivAt (fun r : ℝ => r * d - r ^ 2 * B) d 0 := by
    apply (((hasDerivAt_id 0).mul_const d).sub
      (((hasDerivAt_id 0).pow 2).mul_const B)).congr_deriv
    norm_num
  exact sub_eq_zero.mp (hlocal.hasDerivAt_eq_zero hderiv)

/-- This variation changes both horizontal endpoints by one and preserves
the two top support values. It is a change of width, not a translation. -/
def widthVariation : QuarterPair where
  f := Real.cos
  g := Real.sin
  fD := fun t => -Real.sin t
  gD := Real.cos
  continuous_f := Real.continuous_cos.continuousOn
  continuous_g := Real.continuous_sin.continuousOn
  continuous_fD := Real.continuous_sin.neg.continuousOn
  continuous_gD := Real.continuous_cos.continuousOn
  hasDeriv_f := fun t _ => (Real.hasDerivAt_cos t).hasDerivWithinAt
  hasDeriv_g := fun t _ => (Real.hasDerivAt_sin t).hasDerivWithinAt

theorem QuarterPair.widthTraces_addScaled_widthVariation {u : QuarterPair} {a : ℝ}
    (h : u.WidthTraces a) (r : ℝ) :
    (u.addScaled r widthVariation).WidthTraces (a + r) := by
  rcases h with ⟨hf0, hg0, hfL, hgL⟩
  simp only [QuarterPair.WidthTraces, QuarterPair.addScaled, widthVariation,
    Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two, Real.sin_pi_div_two,
    hf0, hg0, hfL, hgL, mul_one, mul_zero, add_zero, and_self]

def QuarterPair.adjustedP (u : QuarterPair) (t : ℝ) : ℝ := u.p t + min (u.p t) 0

def QuarterPair.adjustedQ (u : QuarterPair) (t : ℝ) : ℝ := u.q t + max (u.q t) 0

theorem adaptiveFirstVariation_widthVariation (u : QuarterPair) {a : ℝ}
    (htrace : u.WidthTraces a)
    (hf : ∀ t ∈ Ioo 0 (Real.pi / 2),
      HasDerivWithinAt u.fluxF (u.forceF t) (Ioi t) t)
    (hg : ∀ t ∈ Ioo 0 (Real.pi / 2),
      HasDerivWithinAt u.fluxG (u.forceG t) (Ioi t) t) :
    adaptiveFirstVariation u widthVariation = u.adjustedP 0 - u.adjustedQ (Real.pi / 2) := by
  rcases htrace with ⟨_, hg0, hfL, _⟩
  rw [adaptiveFirstVariation_eq_boundary u widthVariation hf hg]
  simp only [widthVariation, Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two,
    Real.sin_pi_div_two, mul_zero, mul_one, zero_add, add_zero]
  unfold QuarterPair.fluxF QuarterPair.fluxG QuarterPair.adjustedP QuarterPair.adjustedQ
    QuarterPair.p QuarterPair.q
  rw [hg0, hfL]
  ring

/-- The common-width natural boundary equation, derived from an actual
local maximum among nearby unrestricted width variations. -/
theorem natural_width_boundary (u : QuarterPair) {a ε : ℝ}
    (htrace : u.WidthTraces a) (hε : 0 < ε)
    (hf : ∀ t ∈ Ioo 0 (Real.pi / 2),
      HasDerivWithinAt u.fluxF (u.forceF t) (Ioi t) t)
    (hg : ∀ t ∈ Ioo 0 (Real.pi / 2),
      HasDerivWithinAt u.fluxG (u.forceG t) (Ioi t) t)
    (hmax : ∀ r ∈ Ioo (-ε) ε,
      adaptiveFunctional (u.addScaled r widthVariation) - (a + r) ≤
        adaptiveFunctional u - a) :
    u.adjustedP 0 - u.adjustedQ (Real.pi / 2) = 1 := by
  have hvariation := adaptiveFirstVariation_eq_of_local_max_addScaled u widthVariation
    (c := 1) hε (fun r hr => by linarith [hmax r hr])
  rwa [adaptiveFirstVariation_widthVariation u htrace hf hg] at hvariation

theorem natural_width_boundary_of_momentum_reflection (u : QuarterPair) {a ε : ℝ}
    (htrace : u.WidthTraces a) (hε : 0 < ε)
    (hf : ∀ t ∈ Ioo 0 (Real.pi / 2),
      HasDerivWithinAt u.fluxF (u.forceF t) (Ioi t) t)
    (hg : ∀ t ∈ Ioo 0 (Real.pi / 2),
      HasDerivWithinAt u.fluxG (u.forceG t) (Ioi t) t)
    (hmax : ∀ r ∈ Ioo (-ε) ε,
      adaptiveFunctional (u.addScaled r widthVariation) - (a + r) ≤
        adaptiveFunctional u - a)
    (hreflect : u.adjustedQ (Real.pi / 2) = -u.adjustedP 0) :
    u.adjustedP 0 = 1 / 2 ∧ u.adjustedQ (Real.pi / 2) = -1 / 2 := by
  have h := natural_width_boundary u htrace hε hf hg hmax
  constructor <;> linarith

end AmbidextrousSofa.Analysis
