module

public import AmbidextrousSofa.Analysis.JointSourceFlux
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

@[expose] public section

/-!
# The actual niche derivative from the common spatial flux

The positive and negative cosine projections of the same joint source
measure have finite Radon--Nikodym densities. Their difference is a
measurable integrable derivative of the actual niche on the interior
middle window. On every positive niche interval the sine projection is
Lebesgue measure, so the graph-tangent residual has zero integral over
every measurable spatial subset. No niche differentiability is assumed.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped BoundedContinuousFunction
open scoped ENNReal NNReal
open scoped Topology

namespace AmbidextrousSofa
namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

def weightedSpatialProjection (w : Plane →ᵇ ℝ≥0) : FiniteMeasure ℝ :=
  (weightedFiniteMeasure J.measure w).map Prod.snd

def spatialWeightDensity (w : Plane →ᵇ ℝ≥0) (x : ℝ) : ℝ :=
  ((J.weightedSpatialProjection w : Measure ℝ).rnDeriv volume x).toReal

theorem integrable_spatialWeightDensity (w : Plane →ᵇ ℝ≥0) :
    Integrable (J.spatialWeightDensity w) volume :=
  integrableOn_univ.1 (Measure.integrableOn_toReal_rnDeriv (measure_ne_top _ _))

theorem setIntegral_spatialWeightDensity (w : Plane →ᵇ ℝ≥0)
    {E : Set ℝ} (hE : MeasurableSet E) :
    (∫ x in E, J.spatialWeightDensity w x) =
      ∫ z in univ ×ˢ E, (w z : ℝ) ∂(J.measure : Measure Plane) := by
  have hac : (J.weightedSpatialProjection w : Measure ℝ) ≪ volume :=
    ((weightedFiniteMeasure_absolutelyContinuous J.measure w).map measurable_snd).trans
      J.spatial_marginal_absolutelyContinuous
  unfold spatialWeightDensity
  rw [Measure.setIntegral_toReal_rnDeriv hac, weightedSpatialProjection,
    FiniteMeasure.toMeasure_map, map_measureReal_apply measurable_snd hE, ← univ_prod,
    weightedFiniteMeasure_real_apply _ _ (MeasurableSet.univ.prod hE)]

/-- The sign convention matches the negative-cosine vertical graph flux. -/
def nicheDerivative (x : ℝ) : ℝ :=
  J.spatialWeightDensity (-sourceCosineFunction).nnrealPart x -
    J.spatialWeightDensity sourceCosineFunction.nnrealPart x

theorem measurable_nicheDerivative : Measurable J.nicheDerivative :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal.sub
    (Measure.measurable_rnDeriv _ _).ennreal_toReal

theorem integrable_nicheDerivative : Integrable J.nicheDerivative volume :=
  (J.integrable_spatialWeightDensity _).sub (J.integrable_spatialWeightDensity _)

theorem setIntegral_nicheDerivative {E : Set ℝ} (hE : MeasurableSet E) :
    (∫ x in E, J.nicheDerivative x) =
      ∫ z in univ ×ˢ E, -Real.cos z.1 ∂(J.measure : Measure Plane) := by
  have h := (-sourceCosineFunction).integral_eq_integral_nnrealPart_sub
    ((J.measure : Measure Plane).restrict (univ ×ˢ E))
  rw [neg_neg] at h
  unfold nicheDerivative
  rw [integral_sub (J.integrable_spatialWeightDensity _).integrableOn
      (J.integrable_spatialWeightDensity _).integrableOn,
    J.setIntegral_spatialWeightDensity _ hE, J.setIntegral_spatialWeightDensity _ hE, ← h]
  rfl

/-- The primitive identity supplies an actual derivative almost
everywhere on any interior middle interval. -/
theorem ae_hasDerivAt_niche
    (hTarget : IsDownwardCap target) {l r : ℝ}
    (hbox : Ioo l r ⊆ Icc a b)
    (hmiddle : Ioo l r ⊆ Ioo (horizontalLeft target + capWidth target / 4)
      (horizontalRight target - capWidth target / 4)) :
    ∀ᵐ x ∂volume.restrict (Ioo l r),
      HasDerivAt (sweptNiche target (Real.pi / 2)) (J.nicheDerivative x) x := by
  have hsub {x y : ℝ} (hx : x ∈ Ioo l r) (hy : y ∈ Ioo l r) (hxy : x ≤ y) :
      sweptNiche target (Real.pi / 2) y - sweptNiche target (Real.pi / 2) x =
        ∫ t in x..y, J.nicheDerivative t := by
    rw [intervalIntegral.integral_of_le hxy, J.setIntegral_nicheDerivative measurableSet_Ioc]
    exact J.niche_sub_eq_cosine_integral hTarget (hbox hx) (hbox hy) hxy (hmiddle hx).1
      (hmiddle hy).2
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae
    (LocallyIntegrable.ae_hasDerivAt_integral J.integrable_nicheDerivative.locallyIntegrable)]
    with x hx hd
  refine ((hd x).const_add (sweptNiche target (Real.pi / 2) x)).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  rcases le_total x y with hxy | hyx
  · linarith [hsub hx hy hxy]
  · have := intervalIntegral.integral_symm (f := J.nicheDerivative) (μ := volume) y x
    linarith [hsub hy hx hyx]

theorem ae_sinePart_smul (f : ℝ → ℝ) : ∀ᵐ z ∂(J.measure : Measure Plane),
    sourceSineFunction.nnrealPart z • f z.2 = f z.2 * Real.sin z.1 := by
  filter_upwards [J.ae_angle_mem_upper] with z hz
  change (Real.toNNReal (Real.sin z.1) : ℝ) * f z.2 = f z.2 * Real.sin z.1
  rw [Real.coe_toNNReal _ (Real.sin_pos_of_pos_of_lt_pi hz.1 hz.2).le, mul_comm]

theorem integrable_spatial_sine {f : ℝ → ℝ} (hf : Integrable f volume) :
    Integrable (fun z : Plane => f z.2 * Real.sin z.1) (J.measure : Measure Plane) := by
  have hcomp : Integrable (f ∘ Prod.snd)
      (weightedFiniteMeasure J.measure sourceSineFunction.nnrealPart : Measure Plane) :=
    (hf.mono_measure J.horizontalProjection_le_volume).comp_measurable measurable_snd
  exact ((integrable_withDensity_iff_integrable_smul
    sourceSineFunction.nnrealPart.continuous.measurable).mp hcomp).congr (J.ae_sinePart_smul f)

/-- Exact cancellation against every measurable subset of a positive
interior niche interval. Both fluxes use the original common measure. -/
theorem setIntegral_graph_residual_eq_zero
    (hTarget : IsDownwardCap target) {l r : ℝ}
    (hbox : Ioo l r ⊆ Icc a b)
    (hmiddle : Ioo l r ⊆ Ioo (horizontalLeft target + capWidth target / 4)
      (horizontalRight target - capWidth target / 4))
    (hpositive : ∀ x ∈ Ioo l r, 0 < sweptNiche target (Real.pi / 2) x)
    {E : Set ℝ} (hE : MeasurableSet E) (hEO : E ⊆ Ioo l r) :
    (∫ z in univ ×ˢ E,
      J.nicheDerivative z.2 * Real.sin z.1 + Real.cos z.1
        ∂(J.measure : Measure Plane)) = 0 := by
  have hHE : (J.horizontalProjection : Measure ℝ).restrict E = volume.restrict E := by
    rw [← Measure.restrict_restrict_of_subset hEO,
      J.horizontalProjection_restrict_Ioo_eq_volume_of_positive hTarget hbox hmiddle hpositive,
      Measure.restrict_restrict_of_subset hEO]
  have hsin : (∫ x in E, J.nicheDerivative x ∂(J.horizontalProjection : Measure ℝ)) =
      ∫ z in univ ×ˢ E, J.nicheDerivative z.2 * Real.sin z.1 ∂(J.measure : Measure Plane) := by
    rw [horizontalProjection, sourceHorizontalProjection, FiniteMeasure.toMeasure_map,
      setIntegral_map hE J.measurable_nicheDerivative.aestronglyMeasurable
        measurable_snd.aemeasurable, ← univ_prod, weightedFiniteMeasure_toMeasure,
      setIntegral_withDensity_eq_setIntegral_smul
        sourceSineFunction.nnrealPart.continuous.measurable _ (MeasurableSet.univ.prod hE)]
    exact integral_congr_ae (ae_restrict_of_ae (J.ae_sinePart_smul _))
  have hcos : Integrable (fun z : Plane => Real.cos z.1) (J.measure : Measure Plane) :=
    sourceCosineFunction.integrable _
  rw [integral_add (J.integrable_spatial_sine J.integrable_nicheDerivative).integrableOn
    hcos.integrableOn, ← hsin, hHE, J.setIntegral_nicheDerivative hE, integral_neg,
    neg_add_cancel]

end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
