import AmbidextrousSofa.Analysis.JointSourceFlux
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

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
open scoped Topology

namespace AmbidextrousSofa
namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

def weightedSpatialProjection (w : Plane →ᵇ ℝ≥0) : FiniteMeasure ℝ :=
  (weightedFiniteMeasure J.measure w).map Prod.snd

theorem weightedSpatialProjection_absolutelyContinuous (w : Plane →ᵇ ℝ≥0) :
    (J.weightedSpatialProjection w : Measure ℝ) ≪ volume := by
  have hw := (weightedFiniteMeasure_absolutelyContinuous J.measure w).map measurable_snd
  exact hw.trans J.spatial_marginal_absolutelyContinuous

def spatialWeightDensity (w : Plane →ᵇ ℝ≥0) (x : ℝ) : ℝ :=
  ((J.weightedSpatialProjection w : Measure ℝ).rnDeriv volume x).toReal

theorem measurable_spatialWeightDensity (w : Plane →ᵇ ℝ≥0) :
    Measurable (J.spatialWeightDensity w) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal

theorem integrable_spatialWeightDensity (w : Plane →ᵇ ℝ≥0) :
    Integrable (J.spatialWeightDensity w) volume := by
  have hi := Measure.integrableOn_toReal_rnDeriv
    (μ := (J.weightedSpatialProjection w : Measure ℝ)) (ν := volume)
    (s := univ) (measure_ne_top _ _)
  simpa only [IntegrableOn, Measure.restrict_univ] using hi

theorem setIntegral_spatialWeightDensity (w : Plane →ᵇ ℝ≥0)
    {E : Set ℝ} (hE : MeasurableSet E) :
    (∫ x in E, J.spatialWeightDensity w x) =
      ∫ z in univ ×ˢ E, (w z : ℝ) ∂(J.measure : Measure Plane) := by
  change (∫ x in E,
    ((J.weightedSpatialProjection w : Measure ℝ).rnDeriv volume x).toReal) = _
  rw [Measure.setIntegral_toReal_rnDeriv (J.weightedSpatialProjection_absolutelyContinuous w),
    weightedSpatialProjection, FiniteMeasure.toMeasure_map,
    map_measureReal_apply measurable_snd hE, ← univ_prod,
    weightedFiniteMeasure_real_apply _ _ (MeasurableSet.univ.prod hE)]

/-- The sign convention matches the negative-cosine vertical graph flux. -/
def nicheDerivative (x : ℝ) : ℝ :=
  J.spatialWeightDensity (-sourceCosineFunction).nnrealPart x -
    J.spatialWeightDensity sourceCosineFunction.nnrealPart x

theorem measurable_nicheDerivative : Measurable J.nicheDerivative :=
  (J.measurable_spatialWeightDensity _).sub (J.measurable_spatialWeightDensity _)

theorem integrable_nicheDerivative : Integrable J.nicheDerivative volume :=
  (J.integrable_spatialWeightDensity _).sub (J.integrable_spatialWeightDensity _)

theorem setIntegral_nicheDerivative {E : Set ℝ} (hE : MeasurableSet E) :
    (∫ x in E, J.nicheDerivative x) =
      ∫ z in univ ×ˢ E, -Real.cos z.1 ∂(J.measure : Measure Plane) := by
  rw [nicheDerivative,
    integral_sub (J.integrable_spatialWeightDensity _).integrableOn
      (J.integrable_spatialWeightDensity _).integrableOn,
    J.setIntegral_spatialWeightDensity _ hE, J.setIntegral_spatialWeightDensity _ hE]
  simpa only [neg_neg] using
    ((-sourceCosineFunction).integral_eq_integral_nnrealPart_sub
      ((J.measure : Measure Plane).restrict (univ ×ˢ E))).symm

theorem niche_sub_eq_integral_nicheDerivative
    (hTarget : IsDownwardCap target) {l r : ℝ}
    (hl : l ∈ Icc a b) (hr : r ∈ Icc a b) (hlr : l ≤ r)
    (hL : horizontalLeft target + capWidth target / 4 < l)
    (hR : r < horizontalRight target - capWidth target / 4) :
    sweptNiche target (Real.pi / 2) r - sweptNiche target (Real.pi / 2) l =
      ∫ x in l..r, J.nicheDerivative x := by
  rw [intervalIntegral.integral_of_le hlr,
    J.setIntegral_nicheDerivative measurableSet_Ioc]
  exact J.niche_sub_eq_cosine_integral hTarget hl hr hlr hL hR

/-- The primitive identity supplies an actual derivative almost
everywhere on any interior middle interval. -/
theorem ae_hasDerivAt_niche
    (hTarget : IsDownwardCap target) {l r : ℝ}
    (hbox : Ioo l r ⊆ Icc a b)
    (hmiddle : Ioo l r ⊆ Ioo (horizontalLeft target + capWidth target / 4)
      (horizontalRight target - capWidth target / 4)) :
    ∀ᵐ x ∂volume.restrict (Ioo l r),
      HasDerivAt (sweptNiche target (Real.pi / 2)) (J.nicheDerivative x) x := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae J.integrable_nicheDerivative.locallyIntegrable.ae_hasDerivAt_integral]
    with x hx hd
  apply ((hd x).const_add (sweptNiche target (Real.pi / 2) x)).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  change sweptNiche target (Real.pi / 2) y = sweptNiche target (Real.pi / 2) x +
    ∫ t in x..y, J.nicheDerivative t
  rcases le_total x y with hxy | hyx
  · have h := J.niche_sub_eq_integral_nicheDerivative hTarget
      (hbox hx) (hbox hy) hxy (hmiddle hx).1 (hmiddle hy).2
    linarith only [h]
  · have h := J.niche_sub_eq_integral_nicheDerivative hTarget
      (hbox hy) (hbox hx) hyx (hmiddle hy).1 (hmiddle hx).2
    have hsymm := intervalIntegral.integral_symm (f := J.nicheDerivative) y x
    linarith only [h, hsymm]

theorem setIntegral_spatial_sine {f : ℝ → ℝ} (hf : Measurable f)
    {E : Set ℝ} (hE : MeasurableSet E) :
    (∫ x in E, f x ∂(J.horizontalProjection : Measure ℝ)) =
      ∫ z in univ ×ˢ E, f z.2 * Real.sin z.1 ∂(J.measure : Measure Plane) := by
  rw [horizontalProjection, sourceHorizontalProjection, FiniteMeasure.toMeasure_map,
    setIntegral_map hE hf.aestronglyMeasurable measurable_snd.aemeasurable, ← univ_prod]
  change (∫ z in univ ×ˢ E, f z.2
    ∂(J.measure : Measure Plane).withDensity
      (fun z => (sourceSineFunction.nnrealPart z : ℝ≥0∞))) = _
  rw [setIntegral_withDensity_eq_setIntegral_smul
    sourceSineFunction.nnrealPart.continuous.measurable _ (MeasurableSet.univ.prod hE)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae J.ae_angle_mem_upper] with z hz
  simp only [NNReal.smul_def, smul_eq_mul]
  change (Real.toNNReal (Real.sin z.1) : ℝ) * f z.2 = f z.2 * Real.sin z.1
  rw [Real.coe_toNNReal _ (Real.sin_pos_of_pos_of_lt_pi hz.1 hz.2).le, mul_comm]

theorem integrable_spatial_sine {f : ℝ → ℝ} (hf : Integrable f volume) :
    Integrable (fun z : Plane => f z.2 * Real.sin z.1) (J.measure : Measure Plane) := by
  have hH : Integrable f (J.horizontalProjection : Measure ℝ) :=
    hf.mono_measure J.horizontalProjection_le_volume
  have hcomp : Integrable (f ∘ Prod.snd)
      (weightedFiniteMeasure J.measure sourceSineFunction.nnrealPart : Measure Plane) :=
    hH.comp_measurable measurable_snd
  have hi := (integrable_withDensity_iff_integrable_smul
    sourceSineFunction.nnrealPart.continuous.measurable).mp hcomp
  apply hi.congr
  filter_upwards [J.ae_angle_mem_upper] with z hz
  simp only [Function.comp_apply, NNReal.smul_def, smul_eq_mul]
  change (Real.toNNReal (Real.sin z.1) : ℝ) * f z.2 = f z.2 * Real.sin z.1
  rw [Real.coe_toNNReal _ (Real.sin_pos_of_pos_of_lt_pi hz.1 hz.2).le, mul_comm]

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
  have hHO := J.horizontalProjection_restrict_Ioo_eq_volume_of_positive
    hTarget hbox hmiddle hpositive
  have hHE : (J.horizontalProjection : Measure ℝ).restrict E = volume.restrict E := by
    have h := congrArg (fun μ : Measure ℝ => μ.restrict E) hHO
    simpa only [Measure.restrict_restrict hE, inter_eq_left.mpr hEO] using h
  have hsin := J.setIntegral_spatial_sine J.measurable_nicheDerivative hE
  rw [hHE] at hsin
  have hcos : Integrable (fun z : Plane => Real.cos z.1) (J.measure : Measure Plane) :=
    sourceCosineFunction.integrable _
  rw [integral_add (J.integrable_spatial_sine J.integrable_nicheDerivative).integrableOn
    hcos.integrableOn, ← hsin, J.setIntegral_nicheDerivative hE, integral_neg]
  ring

end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
