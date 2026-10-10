module

public import AmbidextrousSofa.Measure.FiniteMeasurePortmanteau

@[expose] public section

/-!
# Bounded continuous weights on a finite weak limit

Multiplication by one fixed bounded continuous nonnegative weight
preserves weak convergence. The construction retains the underlying
measure exactly as `withDensity`, so spatial restrictions and null sets
can be read directly in the original measure.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped BoundedContinuousFunction
open scoped ENNReal NNReal
open scoped Topology

namespace AmbidextrousSofa

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]

def weightedFiniteMeasure (μ : FiniteMeasure Ω) (w : Ω →ᵇ ℝ≥0) : FiniteMeasure Ω :=
  ⟨(μ : Measure Ω).withDensity (fun x => (w x : ℝ≥0∞)), by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact w.lintegral_lt_top_of_nnreal (μ : Measure Ω)⟩

@[simp]
theorem weightedFiniteMeasure_toMeasure (μ : FiniteMeasure Ω) (w : Ω →ᵇ ℝ≥0) :
    (weightedFiniteMeasure μ w : Measure Ω) =
      (μ : Measure Ω).withDensity (fun x => (w x : ℝ≥0∞)) := rfl

theorem weightedFiniteMeasure_apply (μ : FiniteMeasure Ω) (w : Ω →ᵇ ℝ≥0)
    {E : Set Ω} (hE : MeasurableSet E) :
    (weightedFiniteMeasure μ w : Measure Ω) E = ∫⁻ x in E, (w x : ℝ≥0∞) ∂(μ : Measure Ω) :=
  withDensity_apply _ hE

theorem weightedFiniteMeasure_real_apply [OpensMeasurableSpace Ω]
    (μ : FiniteMeasure Ω) (w : Ω →ᵇ ℝ≥0) {E : Set Ω} (hE : MeasurableSet E) :
    (weightedFiniteMeasure μ w : Measure Ω).real E =
      ∫ x in E, (w x : ℝ) ∂(μ : Measure Ω) := by
  rw [Measure.real, weightedFiniteMeasure_apply μ w hE]
  exact w.toReal_lintegral_coe_eq_integral ((μ : Measure Ω).restrict E)

theorem weightedFiniteMeasure_tendsto [OpensMeasurableSpace Ω]
    {ι : Type*} {L : Filter ι} {μ : FiniteMeasure Ω} {ν : ι → FiniteMeasure Ω}
    (hlim : Tendsto ν L (𝓝 μ)) (w : Ω →ᵇ ℝ≥0) :
    Tendsto (fun i => weightedFiniteMeasure (ν i) w) L (𝓝 (weightedFiniteMeasure μ w)) := by
  apply FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.mpr
  intro f
  have h := FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.mp hlim (w * f)
  simpa only [weightedFiniteMeasure_toMeasure,
    lintegral_withDensity_eq_lintegral_mul _ w.measurable_coe_ennreal_comp
      f.measurable_coe_ennreal_comp,
    Pi.mul_apply, BoundedContinuousFunction.coe_mul, ENNReal.coe_mul] using h

theorem weightedFiniteMeasure_absolutelyContinuous [OpensMeasurableSpace Ω]
    (μ : FiniteMeasure Ω) (w : Ω →ᵇ ℝ≥0) :
    (weightedFiniteMeasure μ w : Measure Ω) ≪ (μ : Measure Ω) :=
  withDensity_absolutelyContinuous _ _

theorem absolutelyContinuous_weightedFiniteMeasure [OpensMeasurableSpace Ω]
    (μ : FiniteMeasure Ω) (w : Ω →ᵇ ℝ≥0)
    (hpos : ∀ᵐ x ∂(μ : Measure Ω), w x ≠ 0) :
    (μ : Measure Ω) ≪ (weightedFiniteMeasure μ w : Measure Ω) := by
  apply withDensity_absolutelyContinuous' w.measurable_coe_ennreal_comp.aemeasurable
  filter_upwards [hpos] with x hx
  exact ENNReal.coe_ne_zero.mpr hx

/-- A bounded continuous test function may be restricted to a set whose
boundary is null for the limiting measure. Positive and negative weights
are passed along the same original weak limit. -/
theorem finiteMeasure_tendsto_setIntegral_boundedContinuous
    [Nonempty Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {ι : Type*} {L : Filter ι} [NeBot L]
    {μ : FiniteMeasure Ω} {ν : ι → FiniteMeasure Ω}
    (hlim : Tendsto ν L (𝓝 μ)) (w : Ω →ᵇ ℝ) {E : Set Ω}
    (hE : MeasurableSet E) (hfrontier : (μ : Measure Ω) (frontier E) = 0) :
    Tendsto (fun i => ∫ x in E, w x ∂(ν i : Measure Ω)) L
      (𝓝 (∫ x in E, w x ∂(μ : Measure Ω))) := by
  have hpos := finiteMeasure_tendsto_real_apply_of_null_frontier
    (weightedFiniteMeasure_tendsto hlim w.nnrealPart)
    (weightedFiniteMeasure_absolutelyContinuous μ w.nnrealPart hfrontier)
  have hneg := finiteMeasure_tendsto_real_apply_of_null_frontier
    (weightedFiniteMeasure_tendsto hlim (-w).nnrealPart)
    (weightedFiniteMeasure_absolutelyContinuous μ (-w).nnrealPart hfrontier)
  have heq (η : FiniteMeasure Ω) :
      (∫ x in E, w x ∂(η : Measure Ω)) =
        (weightedFiniteMeasure η w.nnrealPart : Measure Ω).real E -
          (weightedFiniteMeasure η (-w).nnrealPart : Measure Ω).real E := by
    rw [weightedFiniteMeasure_real_apply η w.nnrealPart hE,
      weightedFiniteMeasure_real_apply η (-w).nnrealPart hE]
    exact w.integral_eq_integral_nnrealPart_sub ((η : Measure Ω).restrict E)
  simpa only [← heq] using hpos.sub hneg

end AmbidextrousSofa
