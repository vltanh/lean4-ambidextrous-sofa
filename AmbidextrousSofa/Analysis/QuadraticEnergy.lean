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

theorem QuarterPair.integrable_normSquare (p : QuarterPair) :
    IntervalIntegrable (fun t => p.f t ^ 2 + p.g t ^ 2) volume 0 (Real.pi / 2) :=
  ContinuousOn.intervalIntegrable_of_Icc (by linarith [Real.pi_pos])
    ((p.continuous_f.pow 2).add (p.continuous_g.pow 2))

theorem QuarterPair.integrable_derivativeSquare (p : QuarterPair) :
    IntervalIntegrable (fun t => p.fD t ^ 2 + p.gD t ^ 2) volume 0 (Real.pi / 2) :=
  ContinuousOn.intervalIntegrable_of_Icc (by linarith [Real.pi_pos])
    ((p.continuous_fD.pow 2).add (p.continuous_gD.pow 2))

theorem QuarterPair.normIntegral_nonneg (p : QuarterPair) : 0 ≤ p.normIntegral :=
  intervalIntegral.integral_nonneg (by linarith [Real.pi_pos])
    (fun t _ => add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem QuarterPair.derivativeIntegral_nonneg (p : QuarterPair) :
    0 ≤ p.derivativeIntegral :=
  intervalIntegral.integral_nonneg (by linarith [Real.pi_pos])
    (fun t _ => add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem QuarterPair.normIntegral_le_derivativeIntegral {p : QuarterPair}
    (h : p.ZeroTraces) : p.normIntegral ≤ 5 / 12 * p.derivativeIntegral := by
  rcases h with ⟨hf0, hg0, hfL, hgL⟩
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hf := quarter_dirichlet_integral_square_le p.continuous_f p.hasDeriv_f
    (ContinuousOn.intervalIntegrable_of_Icc hL p.continuous_fD)
    (ContinuousOn.intervalIntegrable_of_Icc hL (p.continuous_fD.pow 2)) hf0 hfL
  have hg := quarter_dirichlet_integral_square_le p.continuous_g p.hasDeriv_g
    (ContinuousOn.intervalIntegrable_of_Icc hL p.continuous_gD)
    (ContinuousOn.intervalIntegrable_of_Icc hL (p.continuous_gD.pow 2)) hg0 hgL
  have hfi : IntervalIntegrable (fun t => p.f t ^ 2) volume 0 (Real.pi / 2) :=
    ContinuousOn.intervalIntegrable_of_Icc hL (p.continuous_f.pow 2)
  have hgi : IntervalIntegrable (fun t => p.g t ^ 2) volume 0 (Real.pi / 2) :=
    ContinuousOn.intervalIntegrable_of_Icc hL (p.continuous_g.pow 2)
  have hfDi : IntervalIntegrable (fun t => p.fD t ^ 2) volume 0 (Real.pi / 2) :=
    ContinuousOn.intervalIntegrable_of_Icc hL (p.continuous_fD.pow 2)
  have hgDi : IntervalIntegrable (fun t => p.gD t ^ 2) volume 0 (Real.pi / 2) :=
    ContinuousOn.intervalIntegrable_of_Icc hL (p.continuous_gD.pow 2)
  rw [QuarterPair.normIntegral, QuarterPair.derivativeIntegral,
    intervalIntegral.integral_add hfi hgi, intervalIntegral.integral_add hfDi hgDi]
  linarith

theorem quadraticEnergy_eq_gauge (p : QuarterPair) :
    quadraticEnergy p =
      (p.gauge.derivativeIntegral - 9 / 4 * p.gauge.normIntegral) / 2 := by
  have hid :
      (fun t => p.fD t ^ 2 + p.gD t ^ 2 - 2 * (p.f t ^ 2 + p.g t ^ 2) -
        (p.f t * p.gD t - p.g t * p.fD t)) =
      (fun t => p.gauge.fD t ^ 2 + p.gauge.gD t ^ 2 -
        9 / 4 * (p.gauge.f t ^ 2 + p.gauge.g t ^ 2)) :=
    funext (fun t => (p.gauge_energy_identity t).symm)
  unfold quadraticEnergy QuarterPair.derivativeIntegral QuarterPair.normIntegral
  rw [hid, intervalIntegral.integral_sub
    p.gauge.integrable_derivativeSquare (p.gauge.integrable_normSquare.const_mul (9 / 4)),
    intervalIntegral.integral_const_mul]

/-- A positive rational multiple of the gauged derivative energy remains.
The non-sharp coefficient is chosen solely to keep the proof elementary. -/
theorem quadraticEnergy_ge_gauge_derivative {p : QuarterPair} (h : p.ZeroTraces) :
    p.gauge.derivativeIntegral / 32 ≤ quadraticEnergy p := by
  have hbound := QuarterPair.normIntegral_le_derivativeIntegral (p.gauge_zeroTraces h)
  rw [quadraticEnergy_eq_gauge]
  linarith

theorem quadraticEnergy_nonneg {p : QuarterPair} (h : p.ZeroTraces) :
    0 ≤ quadraticEnergy p :=
  (div_nonneg p.gauge.derivativeIntegral_nonneg (by norm_num)).trans
    (quadraticEnergy_ge_gauge_derivative h)

/-- A zero sum of two square integrals forces both actual continuous
coordinates to vanish, rather than merely their almost-everywhere classes. -/
theorem QuarterPair.eqOn_zero_of_normIntegral_eq_zero {p : QuarterPair}
    (h : p.normIntegral = 0) :
    EqOn p.f (fun _ => 0) (Icc 0 (Real.pi / 2)) ∧
      EqOn p.g (fun _ => 0) (Icc 0 (Real.pi / 2)) := by
  have hL : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hfi : IntervalIntegrable (fun t => p.f t ^ 2) volume 0 (Real.pi / 2) :=
    ContinuousOn.intervalIntegrable_of_Icc hL.le (p.continuous_f.pow 2)
  have hgi : IntervalIntegrable (fun t => p.g t ^ 2) volume 0 (Real.pi / 2) :=
    ContinuousOn.intervalIntegrable_of_Icc hL.le (p.continuous_g.pow 2)
  have hfnonneg : 0 ≤ ∫ t in (0 : ℝ)..(Real.pi / 2), p.f t ^ 2 :=
    intervalIntegral.integral_nonneg hL.le (fun t _ => sq_nonneg _)
  have hgnonneg : 0 ≤ ∫ t in (0 : ℝ)..(Real.pi / 2), p.g t ^ 2 :=
    intervalIntegral.integral_nonneg hL.le (fun t _ => sq_nonneg _)
  rw [QuarterPair.normIntegral, intervalIntegral.integral_add hfi hgi] at h
  exact ⟨eqOn_zero_of_integral_square_eq_zero hL p.continuous_f (by linarith),
    eqOn_zero_of_integral_square_eq_zero hL p.continuous_g (by linarith)⟩

/-- Equality in the quadratic estimate has no nonzero fixed-width mode. -/
theorem eqOn_zero_of_quadraticEnergy_eq_zero {p : QuarterPair}
    (htrace : p.ZeroTraces) (henergy : quadraticEnergy p = 0) :
    EqOn p.f (fun _ => 0) (Icc 0 (Real.pi / 2)) ∧
      EqOn p.g (fun _ => 0) (Icc 0 (Real.pi / 2)) := by
  have hcoercive := quadraticEnergy_ge_gauge_derivative htrace
  have hD := p.gauge.derivativeIntegral_nonneg
  have hnorm := QuarterPair.normIntegral_le_derivativeIntegral (p.gauge_zeroTraces htrace)
  have hnorm0 := p.gauge.normIntegral_nonneg
  have hDzero : p.gauge.derivativeIntegral = 0 := by linarith
  have hnormzero : p.gauge.normIntegral = 0 := by rw [hDzero] at hnorm; linarith
  obtain ⟨hf, hg⟩ := p.gauge.eqOn_zero_of_normIntegral_eq_zero hnormzero
  have hpoint : ∀ t ∈ Icc 0 (Real.pi / 2), p.f t = 0 ∧ p.g t = 0 := by
    intro t ht
    have hid := p.gauge_norm_sq t
    rw [hf ht, hg ht] at hid
    have hfsq := sq_nonneg (p.f t)
    have hgsq := sq_nonneg (p.g t)
    constructor <;> apply sq_eq_zero_iff.mp <;> nlinarith
  exact ⟨fun t ht => (hpoint t ht).1, fun t ht => (hpoint t ht).2⟩

theorem quadraticEnergy_pos_of_ne_zero {p : QuarterPair} (htrace : p.ZeroTraces)
    (hne : ∃ t ∈ Icc 0 (Real.pi / 2), p.f t ≠ 0 ∨ p.g t ≠ 0) :
    0 < quadraticEnergy p := by
  have hnonneg := quadraticEnergy_nonneg htrace
  have hnezero : quadraticEnergy p ≠ 0 := by
    intro hzero
    obtain ⟨hf, hg⟩ := eqOn_zero_of_quadraticEnergy_eq_zero htrace hzero
    obtain ⟨t, ht, hne⟩ := hne
    exact hne.elim (fun h => h (hf ht)) (fun h => h (hg ht))
  exact lt_of_le_of_ne hnonneg hnezero.symm

end AmbidextrousSofa.Analysis
