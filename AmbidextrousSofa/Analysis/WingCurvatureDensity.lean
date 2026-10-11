module

public import AmbidextrousSofa.Analysis.WingCurvatureIntervals
public import MovingSofaOptimality.Injectivity.LimitIneq

@[expose] public section

/-!
# Bounded densities of dominated measures

A finite measure dominated by a constant multiple of another has an
actual measurable Radon–Nikodym density. Truncating its null-set values
produces a representative bounded everywhere by the same constant. The
bounded curvature densities on the wings are obtained in this way; no
density or absolute-continuity hypothesis is supplied.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

/-- A finite measure dominated by a finite constant multiple has a
measurable real density with the same everywhere bound. -/
theorem exists_bounded_real_density_of_le_smul
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {C : ℝ} (hC : 0 ≤ C) (hle : μ ≤ ENNReal.ofReal C • ν) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧ (∀ t, 0 ≤ ρ t ∧ ρ t ≤ C) ∧
      μ = ν.withDensity (fun t => ENNReal.ofReal (ρ t)) := by
  have hbound : ∀ᵐ t ∂ν, μ.rnDeriv ν t ≤ ENNReal.ofReal C :=
    ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ.measurable_rnDeriv ν) fun s _ _ => by
      simpa [setLIntegral_const] using (Measure.setLIntegral_rnDeriv_le s).trans (hle s)
  refine ⟨fun t => min (μ.rnDeriv ν t).toReal C,
    (μ.measurable_rnDeriv ν).ennreal_toReal.min measurable_const,
    fun t => ⟨le_min ENNReal.toReal_nonneg hC, min_le_right _ _⟩,
    (Measure.withDensity_rnDeriv_eq μ ν (Measure.absolutelyContinuous_of_le_smul hle)).symm.trans
      (withDensity_congr_ae ?_)⟩
  filter_upwards [Measure.rnDeriv_lt_top μ ν, hbound] with t ht htC
  rw [ENNReal.ofReal_mono.map_min, ENNReal.ofReal_toReal ht.ne, min_eq_left htC]

end AmbidextrousSofa
