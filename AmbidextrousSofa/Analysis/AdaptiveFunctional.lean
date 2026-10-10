module

public import AmbidextrousSofa.Analysis.QuadraticEnergy

@[expose] public section

/-!
# The adaptive functional and its exact Taylor remainder

The two contact losses are the squares of the negative and positive parts
of the actual affine momenta. Their Bregman remainders are nonnegative.
Consequently a stationary pair is the unique maximizer among pairs with the
same four endpoint values. This file proves that analytic implication; it
does not assume or assert existence of a stationary pair at every width, a
global width maximum, or a comparison with the area of an arbitrary cap.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa.Analysis

def negativeSquareBregman (x y : ℝ) : ℝ :=
  min y 0 ^ 2 - min x 0 ^ 2 - 2 * min x 0 * (y - x)

def positiveSquareBregman (x y : ℝ) : ℝ :=
  max y 0 ^ 2 - max x 0 ^ 2 - 2 * max x 0 * (y - x)

theorem negativeSquareBregman_nonneg (x y : ℝ) : 0 ≤ negativeSquareBregman x y := by
  rcases le_total x 0 with hx | hx <;> rcases le_total y 0 with hy | hy
  · simp only [negativeSquareBregman, min_eq_left hx, min_eq_left hy]
    nlinarith [sq_nonneg (y - x)]
  · simp only [negativeSquareBregman, min_eq_left hx, min_eq_right hy]
    nlinarith [sq_nonneg x, mul_nonpos_of_nonpos_of_nonneg hx hy]
  · simp only [negativeSquareBregman, min_eq_right hx, min_eq_left hy]
    nlinarith [sq_nonneg y]
  · simp [negativeSquareBregman, min_eq_right hx, min_eq_right hy]

theorem positiveSquareBregman_nonneg (x y : ℝ) : 0 ≤ positiveSquareBregman x y := by
  rcases le_total x 0 with hx | hx <;> rcases le_total y 0 with hy | hy
  · simp [positiveSquareBregman, max_eq_right hx, max_eq_right hy]
  · simp only [positiveSquareBregman, max_eq_right hx, max_eq_left hy]
    nlinarith [sq_nonneg y]
  · simp only [positiveSquareBregman, max_eq_left hx, max_eq_right hy]
    nlinarith [sq_nonneg x, mul_nonpos_of_nonneg_of_nonpos hx hy]
  · simp only [positiveSquareBregman, max_eq_left hx, max_eq_left hy]
    nlinarith [sq_nonneg (y - x)]

def QuarterPair.p (u : QuarterPair) (t : ℝ) : ℝ := u.fD t - u.g t + 1

def QuarterPair.q (u : QuarterPair) (t : ℝ) : ℝ := u.gD t + u.f t - 1

def adaptiveDensity (u : QuarterPair) (t : ℝ) : ℝ :=
  (u.f t ^ 2 + u.g t ^ 2 - u.fD t ^ 2 - u.gD t ^ 2 +
    (u.f t - 1) ^ 2 + (u.g t - 1) ^ 2 +
    (u.f t - 1) * u.gD t - (u.g t - 1) * u.fD t -
    min (u.p t) 0 ^ 2 - max (u.q t) 0 ^ 2) / 2

def adaptiveFunctional (u : QuarterPair) : ℝ :=
  ∫ t in (0 : ℝ)..(Real.pi / 2), adaptiveDensity u t

def adaptiveLinearDensity (u v : QuarterPair) (t : ℝ) : ℝ :=
  (2 * u.f t - 1) * v.f t + (2 * u.g t - 1) * v.g t -
    u.fD t * v.fD t - u.gD t * v.gD t +
    (v.f t * u.gD t + (u.f t - 1) * v.gD t -
      v.g t * u.fD t - (u.g t - 1) * v.fD t) / 2 -
    min (u.p t) 0 * (v.fD t - v.g t) -
    max (u.q t) 0 * (v.gD t + v.f t)

def adaptiveFirstVariation (u v : QuarterPair) : ℝ :=
  ∫ t in (0 : ℝ)..(Real.pi / 2), adaptiveLinearDensity u v t

def quadraticDensity (v : QuarterPair) (t : ℝ) : ℝ :=
  (v.fD t ^ 2 + v.gD t ^ 2 - 2 * (v.f t ^ 2 + v.g t ^ 2) -
    (v.f t * v.gD t - v.g t * v.fD t)) / 2

def contactDefectDensity (u v : QuarterPair) (t : ℝ) : ℝ :=
  (negativeSquareBregman (u.p t) (v.p t) +
    positiveSquareBregman (u.q t) (v.q t)) / 2

theorem contactDefectDensity_nonneg (u v : QuarterPair) (t : ℝ) :
    0 ≤ contactDefectDensity u v t :=
  div_nonneg (add_nonneg (negativeSquareBregman_nonneg _ _)
    (positiveSquareBregman_nonneg _ _)) (by norm_num)

theorem continuousOn_adaptiveDensity (u : QuarterPair) :
    ContinuousOn (adaptiveDensity u) (Icc 0 (Real.pi / 2)) := by
  have hf := u.continuous_f
  have hg := u.continuous_g
  have hfD := u.continuous_fD
  have hgD := u.continuous_gD
  unfold adaptiveDensity QuarterPair.p QuarterPair.q
  fun_prop

theorem continuousOn_adaptiveLinearDensity (u v : QuarterPair) :
    ContinuousOn (adaptiveLinearDensity u v) (Icc 0 (Real.pi / 2)) := by
  have hf := u.continuous_f
  have hg := u.continuous_g
  have hfD := u.continuous_fD
  have hgD := u.continuous_gD
  have hvf := v.continuous_f
  have hvg := v.continuous_g
  have hvfD := v.continuous_fD
  have hvgD := v.continuous_gD
  unfold adaptiveLinearDensity QuarterPair.p QuarterPair.q
  fun_prop

theorem continuousOn_quadraticDensity (u : QuarterPair) :
    ContinuousOn (quadraticDensity u) (Icc 0 (Real.pi / 2)) := by
  have hf := u.continuous_f
  have hg := u.continuous_g
  have hfD := u.continuous_fD
  have hgD := u.continuous_gD
  unfold quadraticDensity
  fun_prop

theorem continuousOn_contactDefectDensity (u v : QuarterPair) :
    ContinuousOn (contactDefectDensity u v) (Icc 0 (Real.pi / 2)) := by
  have hf := u.continuous_f
  have hg := u.continuous_g
  have hfD := u.continuous_fD
  have hgD := u.continuous_gD
  have hvf := v.continuous_f
  have hvg := v.continuous_g
  have hvfD := v.continuous_fD
  have hvgD := v.continuous_gD
  unfold contactDefectDensity negativeSquareBregman positiveSquareBregman
    QuarterPair.p QuarterPair.q
  fun_prop

/-- Exact pointwise Taylor identity, including both contact remainders.
The differences are actual function and derivative differences. -/
theorem adaptiveDensity_taylor (u v : QuarterPair) (t : ℝ) :
    adaptiveDensity v t = adaptiveDensity u t + adaptiveLinearDensity u (v.sub u) t -
      quadraticDensity (v.sub u) t - contactDefectDensity u v t := by
  unfold adaptiveDensity adaptiveLinearDensity quadraticDensity contactDefectDensity
    negativeSquareBregman positiveSquareBregman QuarterPair.p QuarterPair.q QuarterPair.sub
  ring

theorem quadraticEnergy_eq_integral_density (u : QuarterPair) :
    quadraticEnergy u = ∫ t in (0 : ℝ)..(Real.pi / 2), quadraticDensity u t := by
  unfold quadraticEnergy quadraticDensity
  rw [intervalIntegral.integral_div]

/-- The exact integral remainder. Nonnegative contact terms have not been
dropped, so later equality arguments may recover them separately. -/
theorem adaptiveFunctional_taylor (u v : QuarterPair) :
    adaptiveFunctional v = adaptiveFunctional u + adaptiveFirstVariation u (v.sub u) -
      quadraticEnergy (v.sub u) -
        ∫ t in (0 : ℝ)..(Real.pi / 2), contactDefectDensity u v t := by
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hu := ContinuousOn.intervalIntegrable_of_Icc hL (continuousOn_adaptiveDensity u)
  have hlin := ContinuousOn.intervalIntegrable_of_Icc hL
    (continuousOn_adaptiveLinearDensity u (v.sub u))
  have hquad := ContinuousOn.intervalIntegrable_of_Icc hL
    (continuousOn_quadraticDensity (v.sub u))
  have hcontact := ContinuousOn.intervalIntegrable_of_Icc hL
    (continuousOn_contactDefectDensity u v)
  have hfunction : adaptiveDensity v = fun t =>
      adaptiveDensity u t + adaptiveLinearDensity u (v.sub u) t -
        quadraticDensity (v.sub u) t - contactDefectDensity u v t :=
    funext (adaptiveDensity_taylor u v)
  unfold adaptiveFunctional adaptiveFirstVariation
  rw [hfunction, intervalIntegral.integral_sub ((hu.add hlin).sub hquad) hcontact,
    intervalIntegral.integral_sub (hu.add hlin) hquad,
    intervalIntegral.integral_add hu hlin, ← quadraticEnergy_eq_integral_density]

theorem adaptiveFunctional_le_tangent_sub_quadratic (u v : QuarterPair) :
    adaptiveFunctional v ≤ adaptiveFunctional u + adaptiveFirstVariation u (v.sub u) -
      quadraticEnergy (v.sub u) := by
  have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..(Real.pi / 2), contactDefectDensity u v t :=
    intervalIntegral.integral_nonneg (by linarith [Real.pi_pos])
      (fun t _ => contactDefectDensity_nonneg u v t)
  rw [adaptiveFunctional_taylor u v]
  linarith

/-- Vanishing first variation is the analytic stationary condition. It is
not an assumption about the value of the functional or any geometric area. -/
def QuarterPair.Stationary (u : QuarterPair) : Prop :=
  ∀ v : QuarterPair, v.ZeroTraces → adaptiveFirstVariation u v = 0

theorem adaptiveFunctional_le_of_stationary {u v : QuarterPair}
    (hstationary : u.Stationary) (htraces : v.SameTraces u) :
    adaptiveFunctional v ≤ adaptiveFunctional u := by
  have hzero := QuarterPair.zeroTraces_sub htraces
  have hlin := hstationary (v.sub u) hzero
  have hquad := quadraticEnergy_nonneg hzero
  have hbound := adaptiveFunctional_le_tangent_sub_quadratic u v
  linarith

/-- Strictness at fixed width is literal equality of the two functions on
the closed quarter interval. No conclusion about arbitrary widths is used. -/
theorem eqOn_of_stationary_of_sameTraces_of_ge {u v : QuarterPair}
    (hstationary : u.Stationary) (htraces : v.SameTraces u)
    (hvalue : adaptiveFunctional u ≤ adaptiveFunctional v) :
    EqOn v.f u.f (Icc 0 (Real.pi / 2)) ∧
      EqOn v.g u.g (Icc 0 (Real.pi / 2)) := by
  have hzero := QuarterPair.zeroTraces_sub htraces
  have hlin := hstationary (v.sub u) hzero
  have hquad := quadraticEnergy_nonneg hzero
  have hbound := adaptiveFunctional_le_tangent_sub_quadratic u v
  have heq : quadraticEnergy (v.sub u) = 0 := by linarith
  obtain ⟨hf, hg⟩ := eqOn_zero_of_quadraticEnergy_eq_zero hzero heq
  constructor
  · intro t ht
    have h := hf ht
    exact sub_eq_zero.mp h
  · intro t ht
    have h := hg ht
    exact sub_eq_zero.mp h

end AmbidextrousSofa.Analysis
