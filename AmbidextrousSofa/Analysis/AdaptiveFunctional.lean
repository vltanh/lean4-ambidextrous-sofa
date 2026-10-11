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

attribute [local fun_prop] QuarterPair.continuous_f QuarterPair.continuous_g
  QuarterPair.continuous_fD QuarterPair.continuous_gD

def negativeSquareBregman (x y : ℝ) : ℝ :=
  min y 0 ^ 2 - min x 0 ^ 2 - 2 * min x 0 * (y - x)

def positiveSquareBregman (x y : ℝ) : ℝ :=
  max y 0 ^ 2 - max x 0 ^ 2 - 2 * max x 0 * (y - x)

theorem negativeSquareBregman_nonneg (x y : ℝ) : 0 ≤ negativeSquareBregman x y := by
  rcases le_total x 0 with hx | hx <;> rcases le_total y 0 with hy | hy <;>
    simp only [negativeSquareBregman, min_eq_left, min_eq_right, hx, hy] <;>
    nlinarith [sq_nonneg (y - x)]

theorem positiveSquareBregman_nonneg (x y : ℝ) : 0 ≤ positiveSquareBregman x y := by
  rcases le_total x 0 with hx | hx <;> rcases le_total y 0 with hy | hy <;>
    simp only [positiveSquareBregman, max_eq_left, max_eq_right, hx, hy] <;>
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

theorem continuousOn_adaptiveDensity (u : QuarterPair) :
    ContinuousOn (adaptiveDensity u) (Icc 0 (Real.pi / 2)) := by
  unfold adaptiveDensity QuarterPair.p QuarterPair.q; simp only [sq]; fun_prop

theorem continuousOn_adaptiveLinearDensity (u v : QuarterPair) :
    ContinuousOn (adaptiveLinearDensity u v) (Icc 0 (Real.pi / 2)) := by
  unfold adaptiveLinearDensity QuarterPair.p QuarterPair.q; fun_prop

/-- Exact pointwise Taylor identity, including both contact remainders.
The differences are actual function and derivative differences. -/
theorem adaptiveDensity_taylor (u v : QuarterPair) (t : ℝ) :
    adaptiveDensity v t = adaptiveDensity u t + adaptiveLinearDensity u (v.sub u) t -
      quadraticDensity (v.sub u) t - (negativeSquareBregman (u.p t) (v.p t) +
        positiveSquareBregman (u.q t) (v.q t)) / 2 := by
  unfold adaptiveDensity adaptiveLinearDensity quadraticDensity
    negativeSquareBregman positiveSquareBregman QuarterPair.p QuarterPair.q QuarterPair.sub
  ring

theorem adaptiveFunctional_le_tangent_sub_quadratic (u v : QuarterPair) :
    adaptiveFunctional v ≤ adaptiveFunctional u + adaptiveFirstVariation u (v.sub u) -
      quadraticEnergy (v.sub u) := by
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hu := (continuousOn_adaptiveDensity u).intervalIntegrable_of_Icc (μ := volume) hL
  have hlin := (continuousOn_adaptiveLinearDensity u (v.sub u)).intervalIntegrable_of_Icc
    (μ := volume) hL
  have hquad : IntervalIntegrable (quadraticDensity (v.sub u)) volume 0 (Real.pi / 2) :=
    ContinuousOn.intervalIntegrable_of_Icc hL (by unfold quadraticDensity; simp only [sq]; fun_prop)
  have hq : quadraticEnergy (v.sub u) =
      ∫ t in (0 : ℝ)..(Real.pi / 2), quadraticDensity (v.sub u) t :=
    (intervalIntegral.integral_div _ _).symm
  unfold adaptiveFunctional adaptiveFirstVariation
  rw [hq, ← intervalIntegral.integral_add hu hlin,
    ← intervalIntegral.integral_sub (hu.add hlin) hquad]
  refine intervalIntegral.integral_mono_on hL
    ((continuousOn_adaptiveDensity v).intervalIntegrable_of_Icc hL) ((hu.add hlin).sub hquad)
    fun t _ => ?_
  linarith [adaptiveDensity_taylor u v t, negativeSquareBregman_nonneg (u.p t) (v.p t),
    positiveSquareBregman_nonneg (u.q t) (v.q t)]

/-- Vanishing first variation is the analytic stationary condition. It is
not an assumption about the value of the functional or any geometric area. -/
def QuarterPair.Stationary (u : QuarterPair) : Prop :=
  ∀ v : QuarterPair, v.ZeroTraces → adaptiveFirstVariation u v = 0

theorem adaptiveFunctional_le_of_stationary {u v : QuarterPair}
    (hstationary : u.Stationary) (htraces : v.SameTraces u) :
    adaptiveFunctional v ≤ adaptiveFunctional u := by
  have hzero := QuarterPair.zeroTraces_sub htraces
  linarith [hstationary (v.sub u) hzero, quadraticEnergy_nonneg hzero,
    adaptiveFunctional_le_tangent_sub_quadratic u v]

/-- Strictness at fixed width is literal equality of the two functions on
the closed quarter interval. No conclusion about arbitrary widths is used. -/
theorem eqOn_of_stationary_of_sameTraces_of_ge {u v : QuarterPair}
    (hstationary : u.Stationary) (htraces : v.SameTraces u)
    (hvalue : adaptiveFunctional u ≤ adaptiveFunctional v) :
    EqOn v.f u.f (Icc 0 (Real.pi / 2)) ∧
      EqOn v.g u.g (Icc 0 (Real.pi / 2)) := by
  have hzero := QuarterPair.zeroTraces_sub htraces
  obtain ⟨hf, hg⟩ := eqOn_zero_of_quadraticEnergy_eq_zero hzero <| by
    linarith [hstationary (v.sub u) hzero, quadraticEnergy_nonneg hzero,
      adaptiveFunctional_le_tangent_sub_quadratic u v]
  exact ⟨fun t ht => sub_eq_zero.mp (hf ht), fun t ht => sub_eq_zero.mp (hg ht)⟩

end AmbidextrousSofa.Analysis
