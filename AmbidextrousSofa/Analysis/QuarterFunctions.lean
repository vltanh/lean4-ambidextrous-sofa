module

public import AmbidextrousSofa.Analysis.DirichletEnergy

@[expose] public section

/-!
# Pairs of continuously differentiable quarter-interval functions

These data record functions and their actual right derivatives. They impose
no convexity, support, maximization, area, or calibration conclusion. The
quarter interval is closed for continuity and open for differentiation, so
piecewise twice differentiable reference coordinates belong to this domain.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa.Analysis

structure QuarterPair where
  f : ℝ → ℝ
  g : ℝ → ℝ
  fD : ℝ → ℝ
  gD : ℝ → ℝ
  continuous_f : ContinuousOn f (Icc 0 (Real.pi / 2))
  continuous_g : ContinuousOn g (Icc 0 (Real.pi / 2))
  continuous_fD : ContinuousOn fD (Icc 0 (Real.pi / 2))
  continuous_gD : ContinuousOn gD (Icc 0 (Real.pi / 2))
  hasDeriv_f : ∀ t ∈ Ioo 0 (Real.pi / 2), HasDerivWithinAt f (fD t) (Ioi t) t
  hasDeriv_g : ∀ t ∈ Ioo 0 (Real.pi / 2), HasDerivWithinAt g (gD t) (Ioi t) t

/-- All four traces vanish; these are precisely fixed-width variations. -/
def QuarterPair.ZeroTraces (p : QuarterPair) : Prop :=
  p.f 0 = 0 ∧ p.g 0 = 0 ∧ p.f (Real.pi / 2) = 0 ∧ p.g (Real.pi / 2) = 0

/-- Equal endpoint values, including the two width-dependent traces. -/
def QuarterPair.SameTraces (p q : QuarterPair) : Prop :=
  p.f 0 = q.f 0 ∧ p.g 0 = q.g 0 ∧
    p.f (Real.pi / 2) = q.f (Real.pi / 2) ∧ p.g (Real.pi / 2) = q.g (Real.pi / 2)

def QuarterPair.sub (p q : QuarterPair) : QuarterPair where
  f := fun t => p.f t - q.f t
  g := fun t => p.g t - q.g t
  fD := fun t => p.fD t - q.fD t
  gD := fun t => p.gD t - q.gD t
  continuous_f := p.continuous_f.sub q.continuous_f
  continuous_g := p.continuous_g.sub q.continuous_g
  continuous_fD := p.continuous_fD.sub q.continuous_fD
  continuous_gD := p.continuous_gD.sub q.continuous_gD
  hasDeriv_f := fun t ht => (p.hasDeriv_f t ht).sub (q.hasDeriv_f t ht)
  hasDeriv_g := fun t ht => (p.hasDeriv_g t ht).sub (q.hasDeriv_g t ht)

theorem QuarterPair.zeroTraces_sub {p q : QuarterPair} (h : p.SameTraces q) :
    (p.sub q).ZeroTraces :=
  ⟨sub_eq_zero.2 h.1, sub_eq_zero.2 h.2.1, sub_eq_zero.2 h.2.2.1, sub_eq_zero.2 h.2.2.2⟩

/-- Multiplication by the half-angle rotation `exp (-i t / 2)`, written in
real coordinates. Its derivative includes the derivative of the rotation. -/
def QuarterPair.gauge (p : QuarterPair) : QuarterPair where
  f := fun t => Real.cos (t / 2) * p.f t + Real.sin (t / 2) * p.g t
  g := fun t => Real.cos (t / 2) * p.g t - Real.sin (t / 2) * p.f t
  fD := fun t => Real.cos (t / 2) * p.fD t + Real.sin (t / 2) * p.gD t +
    (Real.cos (t / 2) * p.g t - Real.sin (t / 2) * p.f t) / 2
  gD := fun t => Real.cos (t / 2) * p.gD t - Real.sin (t / 2) * p.fD t -
    (Real.cos (t / 2) * p.f t + Real.sin (t / 2) * p.g t) / 2
  continuous_f := by have := p.continuous_f; have := p.continuous_g; fun_prop
  continuous_g := by have := p.continuous_f; have := p.continuous_g; fun_prop
  continuous_fD := by
    have := p.continuous_f; have := p.continuous_g; have := p.continuous_fD
    have := p.continuous_gD; fun_prop
  continuous_gD := by
    have := p.continuous_f; have := p.continuous_g; have := p.continuous_fD
    have := p.continuous_gD; fun_prop
  hasDeriv_f := by
    intro t ht
    have hc := ((hasDerivAt_id t).div_const 2).cos.hasDerivWithinAt (s := Ioi t)
    have hs := ((hasDerivAt_id t).div_const 2).sin.hasDerivWithinAt (s := Ioi t)
    exact ((hc.mul (p.hasDeriv_f t ht)).add (hs.mul (p.hasDeriv_g t ht))).congr_deriv
      (by simp only [id]; ring)
  hasDeriv_g := by
    intro t ht
    have hc := ((hasDerivAt_id t).div_const 2).cos.hasDerivWithinAt (s := Ioi t)
    have hs := ((hasDerivAt_id t).div_const 2).sin.hasDerivWithinAt (s := Ioi t)
    exact ((hc.mul (p.hasDeriv_g t ht)).sub (hs.mul (p.hasDeriv_f t ht))).congr_deriv
      (by simp only [id]; ring)

theorem QuarterPair.gauge_zeroTraces {p : QuarterPair} (h : p.ZeroTraces) :
    p.gauge.ZeroTraces := by
  simp_all [QuarterPair.ZeroTraces, QuarterPair.gauge]

theorem QuarterPair.gauge_norm_sq (p : QuarterPair) (t : ℝ) :
    p.gauge.f t ^ 2 + p.gauge.g t ^ 2 = p.f t ^ 2 + p.g t ^ 2 := by
  dsimp only [QuarterPair.gauge]
  linear_combination (p.f t ^ 2 + p.g t ^ 2) * Real.sin_sq_add_cos_sq (t / 2)

/-- The skew derivative term becomes an ordinary Dirichlet energy after
the half-angle rotation. This is a pointwise polynomial identity. -/
theorem QuarterPair.gauge_energy_identity (p : QuarterPair) (t : ℝ) :
    p.gauge.fD t ^ 2 + p.gauge.gD t ^ 2 -
        9 / 4 * (p.gauge.f t ^ 2 + p.gauge.g t ^ 2) =
      p.fD t ^ 2 + p.gD t ^ 2 - 2 * (p.f t ^ 2 + p.g t ^ 2) -
        (p.f t * p.gD t - p.g t * p.fD t) := by
  dsimp only [QuarterPair.gauge]
  linear_combination (p.fD t ^ 2 + p.gD t ^ 2 - 2 * (p.f t ^ 2 + p.g t ^ 2) -
    (p.f t * p.gD t - p.g t * p.fD t)) * Real.sin_sq_add_cos_sq (t / 2)

end AmbidextrousSofa.Analysis
