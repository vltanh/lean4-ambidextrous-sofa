module

public import AmbidextrousSofa.Analysis.QuarterFunctions

@[expose] public section

/-!
# Strict quadratic energy on the quarter interval

The elementary two-endpoint Dirichlet estimate is sufficient for strict
positivity of the adaptive functional's quadratic remainder. The proof uses
the actual derivative of the half-angle gauge, including its skew term.
Equality recovers the functions at every point of the closed interval.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa.Analysis

def QuarterPair.normIntegral (p : QuarterPair) : ℝ :=
  ∫ t in (0 : ℝ)..(Real.pi / 2), p.f t ^ 2 + p.g t ^ 2

def QuarterPair.derivativeIntegral (p : QuarterPair) : ℝ :=
  ∫ t in (0 : ℝ)..(Real.pi / 2), p.fD t ^ 2 + p.gD t ^ 2

def quadraticEnergy (p : QuarterPair) : ℝ :=
  (∫ t in (0 : ℝ)..(Real.pi / 2),
    p.fD t ^ 2 + p.gD t ^ 2 - 2 * (p.f t ^ 2 + p.g t ^ 2) -
      (p.f t * p.gD t - p.g t * p.fD t)) / 2

theorem integral_sq_add_sq {u v : ℝ → ℝ} (hu : ContinuousOn u (Icc 0 (Real.pi / 2)))
    (hv : ContinuousOn v (Icc 0 (Real.pi / 2))) :
    ∫ t in (0 : ℝ)..(Real.pi / 2), u t ^ 2 + v t ^ 2 =
      (∫ t in (0 : ℝ)..(Real.pi / 2), u t ^ 2) + ∫ t in (0 : ℝ)..(Real.pi / 2), v t ^ 2 :=
  intervalIntegral.integral_add ((hu.pow 2).intervalIntegrable_of_Icc (by positivity))
    ((hv.pow 2).intervalIntegrable_of_Icc (by positivity))

theorem QuarterPair.normIntegral_le_derivativeIntegral {p : QuarterPair}
    (h : p.ZeroTraces) : p.normIntegral ≤ 5 / 12 * p.derivativeIntegral := by
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  rw [normIntegral, derivativeIntegral, integral_sq_add_sq p.continuous_f p.continuous_g,
    integral_sq_add_sq p.continuous_fD p.continuous_gD]
  linarith [quarter_dirichlet_integral_square_le p.continuous_f p.hasDeriv_f
      (p.continuous_fD.intervalIntegrable_of_Icc hL)
      ((p.continuous_fD.pow 2).intervalIntegrable_of_Icc hL) h.1 h.2.2.1,
    quarter_dirichlet_integral_square_le p.continuous_g p.hasDeriv_g
      (p.continuous_gD.intervalIntegrable_of_Icc hL)
      ((p.continuous_gD.pow 2).intervalIntegrable_of_Icc hL) h.2.1 h.2.2.2]

theorem quadraticEnergy_eq_gauge (p : QuarterPair) :
    quadraticEnergy p =
      (p.gauge.derivativeIntegral - 9 / 4 * p.gauge.normIntegral) / 2 := by
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  simp only [quadraticEnergy, QuarterPair.derivativeIntegral, QuarterPair.normIntegral,
    ← p.gauge_energy_identity, ← intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub]
  · exact ((p.gauge.continuous_fD.pow 2).add
      (p.gauge.continuous_gD.pow 2)).intervalIntegrable_of_Icc hL
  · exact (continuousOn_const.mul ((p.gauge.continuous_f.pow 2).add
      (p.gauge.continuous_g.pow 2))).intervalIntegrable_of_Icc hL

/-- A positive rational multiple of the gauged derivative energy remains.
The non-sharp coefficient is chosen solely to keep the proof elementary. -/
theorem quadraticEnergy_ge_gauge_derivative {p : QuarterPair} (h : p.ZeroTraces) :
    p.gauge.derivativeIntegral / 32 ≤ quadraticEnergy p := by
  rw [quadraticEnergy_eq_gauge]
  linarith [QuarterPair.normIntegral_le_derivativeIntegral (p.gauge_zeroTraces h)]

theorem QuarterPair.derivativeIntegral_nonneg (p : QuarterPair) : 0 ≤ p.derivativeIntegral :=
  intervalIntegral.integral_nonneg (by positivity) fun _ _ => by positivity

theorem quadraticEnergy_nonneg {p : QuarterPair} (h : p.ZeroTraces) :
    0 ≤ quadraticEnergy p :=
  (div_nonneg p.gauge.derivativeIntegral_nonneg (by norm_num)).trans
    (quadraticEnergy_ge_gauge_derivative h)

/-- Equality in the quadratic estimate has no nonzero fixed-width mode. -/
theorem eqOn_zero_of_quadraticEnergy_eq_zero {p : QuarterPair}
    (htrace : p.ZeroTraces) (henergy : quadraticEnergy p = 0) :
    EqOn p.f (fun _ => 0) (Icc 0 (Real.pi / 2)) ∧
      EqOn p.g (fun _ => 0) (Icc 0 (Real.pi / 2)) := by
  have hL : (0 : ℝ) < Real.pi / 2 := by positivity
  have hnorm := QuarterPair.normIntegral_le_derivativeIntegral (p.gauge_zeroTraces htrace)
  have := quadraticEnergy_ge_gauge_derivative htrace
  have := p.gauge.derivativeIntegral_nonneg
  rw [QuarterPair.normIntegral, integral_sq_add_sq p.gauge.continuous_f p.gauge.continuous_g]
    at hnorm
  have hf := intervalIntegral.integral_nonneg (μ := volume) hL.le fun t _ =>
    sq_nonneg (p.gauge.f t)
  have hg := intervalIntegral.integral_nonneg (μ := volume) hL.le fun t _ =>
    sq_nonneg (p.gauge.g t)
  have hf0 := eqOn_zero_of_integral_square_eq_zero hL p.gauge.continuous_f (by linarith)
  have hg0 := eqOn_zero_of_integral_square_eq_zero hL p.gauge.continuous_g (by linarith)
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩ <;>
    nlinarith [p.gauge_norm_sq t, hf0 ht, hg0 ht, sq_nonneg (p.f t), sq_nonneg (p.g t)]

end AmbidextrousSofa.Analysis
