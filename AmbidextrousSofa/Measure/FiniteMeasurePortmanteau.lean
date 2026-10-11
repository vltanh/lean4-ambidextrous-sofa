module

public import Mathlib.MeasureTheory.Measure.Portmanteau

@[expose] public section

/-!
# Open-set and null-boundary limits for finite measures

The open-set half of Portmanteau is obtained by normalizing the nonzero
limit and retaining the convergent total masses. The zero limit is
immediate. This gives setwise convergence at every null boundary without
assuming that the finite measures are probability measures.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal NNReal
open scoped Topology

namespace AmbidextrousSofa

variable {Ω ι : Type*} [Nonempty Ω] [MeasurableSpace Ω] [TopologicalSpace Ω]
  [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
  {L : Filter ι} [NeBot L] {μ : FiniteMeasure Ω} {ν : ι → FiniteMeasure Ω}

theorem finiteMeasure_le_liminf_open_of_tendsto (hlim : Tendsto ν L (𝓝 μ)) {G : Set Ω}
    (hG : IsOpen G) : (μ : Measure Ω) G ≤ liminf (fun i => (ν i : Measure Ω) G) L := by
  rcases eq_or_ne μ 0 with rfl | hμ
  · simp
  have hscale (η : FiniteMeasure Ω) :
      (η : Measure Ω) G = (η.mass : ℝ≥0∞) * (η.normalize : Measure Ω) G := by
    rw [← η.ennreal_coeFn_eq_coeFn_toMeasure G, η.self_eq_mass_mul_normalize G,
      ENNReal.coe_mul, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  have hmass : Tendsto (fun i => ((ν i).mass : ℝ≥0∞)) L (𝓝 (μ.mass : ℝ≥0∞)) :=
    (ENNReal.continuous_coe.tendsto μ.mass).comp hlim.mass
  simp only [hscale]
  calc _ ≤ (μ.mass : ℝ≥0∞) * liminf (fun i => ((ν i).normalize : Measure Ω) G) L :=
        mul_le_mul_right (ProbabilityMeasure.le_liminf_measure_open_of_tendsto
          (FiniteMeasure.tendsto_normalize_of_tendsto hlim hμ) hG) _
    _ = liminf (fun i => ((ν i).mass : ℝ≥0∞)) L *
        liminf (fun i => ((ν i).normalize : Measure Ω) G) L := by rw [hmass.liminf_eq]
    _ ≤ _ := ENNReal.le_liminf_mul

theorem finiteMeasure_tendsto_real_apply_of_null_frontier (hlim : Tendsto ν L (𝓝 μ)) {E : Set Ω}
    (hE : (μ : Measure Ω) (frontier E) = 0) :
    Tendsto (fun i => (ν i : Measure Ω).real E) L (𝓝 ((μ : Measure Ω).real E)) :=
  (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
    (tendsto_measure_of_le_liminf_measure_of_limsup_measure_le interior_subset subset_closure hE
      (finiteMeasure_le_liminf_open_of_tendsto hlim isOpen_interior)
      (FiniteMeasure.limsup_measure_closed_le_of_tendsto hlim isClosed_closure))

/-- A uniform asymptotic bound on an open set passes to the finite weak
limit. Only the scalar bounds need converge pointwise along the filter. -/
theorem finiteMeasure_real_open_le_of_tendsto_bound (hlim : Tendsto ν L (𝓝 μ)) {G : Set Ω}
    (hG : IsOpen G) {B : ι → ℝ} {b : ℝ} (hb : 0 ≤ b) (hB : Tendsto B L (𝓝 b))
    (hbound : ∀ᶠ i in L, (ν i : Measure Ω).real G ≤ B i) :
    (μ : Measure Ω).real G ≤ b := by
  have hENN : ∀ᶠ i in L, (ν i : Measure Ω) G ≤ ENNReal.ofReal (B i) := hbound.mono fun _ hi =>
    (ofReal_measureReal (measure_ne_top _ _)).symm.trans_le (ENNReal.ofReal_le_ofReal hi)
  exact ENNReal.toReal_le_of_le_ofReal hb ((finiteMeasure_le_liminf_open_of_tendsto hlim hG).trans
    ((liminf_le_liminf hENN).trans_eq ((ENNReal.continuous_ofReal.tendsto b).comp hB).liminf_eq))

end AmbidextrousSofa
