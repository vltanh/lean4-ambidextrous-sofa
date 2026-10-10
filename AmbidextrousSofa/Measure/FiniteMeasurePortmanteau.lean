import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Open-set and null-boundary limits for finite measures

The open-set half of Portmanteau is obtained by normalizing the nonzero
limit and retaining the convergent total masses. The zero limit is
immediate. This gives setwise convergence at every null boundary without
assuming that the finite measures are probability measures.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem finiteMeasure_le_liminf_open_of_tendsto
    {Ω ι : Type*} [Nonempty Ω] [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {L : Filter ι} [NeBot L] {μ : FiniteMeasure Ω} {ν : ι → FiniteMeasure Ω}
    (hlim : Tendsto ν L (𝓝 μ)) {G : Set Ω} (hG : IsOpen G) :
    (μ : Measure Ω) G ≤ liminf (fun i => (ν i : Measure Ω) G) L := by
  rcases eq_or_ne μ 0 with rfl | hμ
  · simp only [FiniteMeasure.toMeasure_zero, Measure.zero_apply, zero_le]
  have hscale (η : FiniteMeasure Ω) :
      (η : Measure Ω) G = (η.mass : ℝ≥0∞) * (η.normalize : Measure Ω) G := by
    rw [← η.ennreal_coeFn_eq_coeFn_toMeasure G, η.self_eq_mass_mul_normalize G,
      ENNReal.coe_mul, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  have hmass : Tendsto (fun i => ((ν i).mass : ℝ≥0∞)) L (𝓝 (μ.mass : ℝ≥0∞)) :=
    (ENNReal.continuous_coe.tendsto μ.mass).comp hlim.mass
  have hnorm := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    (FiniteMeasure.tendsto_normalize_of_tendsto hlim hμ) hG
  calc
    (μ : Measure Ω) G = (μ.mass : ℝ≥0∞) * (μ.normalize : Measure Ω) G := hscale μ
    _ ≤ (μ.mass : ℝ≥0∞) * liminf (fun i => ((ν i).normalize : Measure Ω) G) L :=
      mul_le_mul_left' hnorm _
    _ = liminf (fun i => ((ν i).mass : ℝ≥0∞)) L *
        liminf (fun i => ((ν i).normalize : Measure Ω) G) L := by rw [hmass.liminf_eq]
    _ ≤ liminf (fun i => ((ν i).mass : ℝ≥0∞) * ((ν i).normalize : Measure Ω) G) L :=
      ENNReal.le_liminf_mul
    _ = liminf (fun i => (ν i : Measure Ω) G) L := by simp only [← hscale]

theorem finiteMeasure_tendsto_apply_of_null_frontier
    {Ω ι : Type*} [Nonempty Ω] [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {L : Filter ι} [NeBot L] {μ : FiniteMeasure Ω} {ν : ι → FiniteMeasure Ω}
    (hlim : Tendsto ν L (𝓝 μ)) {E : Set Ω}
    (hE : (μ : Measure Ω) (frontier E) = 0) :
    Tendsto (fun i => (ν i : Measure Ω) E) L (𝓝 ((μ : Measure Ω) E)) :=
  tendsto_measure_of_le_liminf_measure_of_limsup_measure_le
    interior_subset subset_closure hE
    (finiteMeasure_le_liminf_open_of_tendsto hlim isOpen_interior)
    (FiniteMeasure.limsup_measure_closed_le_of_tendsto hlim isClosed_closure)

theorem finiteMeasure_tendsto_real_apply_of_null_frontier
    {Ω ι : Type*} [Nonempty Ω] [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {L : Filter ι} [NeBot L] {μ : FiniteMeasure Ω} {ν : ι → FiniteMeasure Ω}
    (hlim : Tendsto ν L (𝓝 μ)) {E : Set Ω}
    (hE : (μ : Measure Ω) (frontier E) = 0) :
    Tendsto (fun i => (ν i : Measure Ω).real E) L (𝓝 ((μ : Measure Ω).real E)) :=
  (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
    (finiteMeasure_tendsto_apply_of_null_frontier hlim hE)

/-- A uniform asymptotic bound on an open set passes to the finite weak
limit. Only the scalar bounds need converge pointwise along the filter. -/
theorem finiteMeasure_real_open_le_of_tendsto_bound
    {Ω ι : Type*} [Nonempty Ω] [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {L : Filter ι} [NeBot L] {μ : FiniteMeasure Ω} {ν : ι → FiniteMeasure Ω}
    (hlim : Tendsto ν L (𝓝 μ)) {G : Set Ω} (hG : IsOpen G)
    {B : ι → ℝ} {b : ℝ} (hb : 0 ≤ b) (hB : Tendsto B L (𝓝 b))
    (hbound : ∀ᶠ i in L, (ν i : Measure Ω).real G ≤ B i) :
    (μ : Measure Ω).real G ≤ b := by
  have hlimB := (ENNReal.continuous_ofReal.tendsto b).comp hB
  have hENN : ∀ᶠ i in L, (ν i : Measure Ω) G ≤ ENNReal.ofReal (B i) := by
    filter_upwards [hbound] with i hi
    simpa only [ofReal_measureReal] using ENNReal.ofReal_le_ofReal hi
  have h := (finiteMeasure_le_liminf_open_of_tendsto hlim hG).trans
    ((liminf_le_liminf hENN).trans_eq hlimB.liminf_eq)
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [ENNReal.toReal_ofReal hb] using hr

end AmbidextrousSofa
