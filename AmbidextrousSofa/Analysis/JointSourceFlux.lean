module

public import AmbidextrousSofa.Analysis.JointSourceSpatial
public import AmbidextrousSofa.Analysis.SourceLocalization

@[expose] public section

/-!
# The two spatial fluxes of the actual common source limit

Both coordinates of the sampled niche graph pass through the same
joint source measure. On a compact interval inside the middle window,
the negative cosine flux is the actual niche increment. Where the
actual niche is positive, the sine flux is the entire horizontal
length. The unweighted spatial marginal is absolutely continuous as
well, because the sine weight is strictly positive almost everywhere.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped BoundedContinuousFunction
open scoped Topology

namespace AmbidextrousSofa
namespace AngularGrid

open FinitePolygon

theorem finiteBarrier_sub_eq_joint_cosine_integral
    (U : Set Plane) (grid : Finset QuarterAngle) {l r : ℝ} (hlr : l ≤ r) :
    finiteBarrier U (normal grid) (pairList grid) none r -
        finiteBarrier U (normal grid) (pairList grid) none l =
      ∫ z : Plane, -Real.cos z.1 ∂innerJointMeasure U grid l r := by
  have h := finiteBarrier_projection_eq_joint_integral U grid hlr (Real.pi / 2)
  simpa only [Real.cos_pi_div_two, Real.sin_pi_div_two, zero_mul, one_mul, zero_add,
    Real.sin_sub, mul_zero, mul_one, zero_sub] using h

namespace SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

theorem spatial_marginal_absolutelyContinuous :
    (J.measure : Measure Plane).map Prod.snd ≪ (volume : Measure ℝ) :=
  ((absolutelyContinuous_weightedFiniteMeasure J.measure sourceSineFunction.nnrealPart
    J.sinePart_ne_zero_ae).map measurable_snd).trans
      (Measure.absolutelyContinuous_of_le J.horizontalProjection_le_volume)

theorem horizontalProjection_real_eq_sine_integral {E : Set ℝ} (hE : MeasurableSet E) :
    (J.horizontalProjection : Measure ℝ).real E =
      ∫ z in univ ×ˢ E, Real.sin z.1 ∂(J.measure : Measure Plane) := by
  rw [horizontalProjection, sourceHorizontalProjection, FiniteMeasure.toMeasure_map,
    map_measureReal_apply measurable_snd hE, ← univ_prod,
    weightedFiniteMeasure_real_apply _ _ (MeasurableSet.univ.prod hE)]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae J.ae_angle_mem_upper] with z hz
  exact Real.coe_toNNReal _ (Real.sin_pos_of_mem_Ioo hz).le

theorem local_test_integral_tendsto
    (hTarget : IsDownwardCap target) (w : Plane →ᵇ ℝ) {l r : ℝ}
    (hL : horizontalLeft target + capWidth target / 4 < l)
    (hR : r < horizontalRight target - capWidth target / 4) :
    Tendsto (fun n => ∫ z, w z ∂innerJointMeasure (J.caps n) (dyadic (J.level n)) l r)
      (sourceLimitFilter : Filter ℕ)
      (𝓝 (∫ z in univ ×ˢ Ioc l r, w z ∂(J.measure : Measure Plane))) := by
  have hl := J.hausdorff.horizontalLeft_tendsto (fun n => (J.isCap n).isCompact)
    (fun n => (J.isCap n).nonempty) hTarget.isCompact hTarget.nonempty
  have hr := J.hausdorff.horizontalRight_tendsto (fun n => (J.isCap n).isCompact)
    (fun n => (J.isCap n).nonempty) hTarget.isCompact hTarget.nonempty
  have hw := (J.hausdorff.capWidth_tendsto J.isCap hTarget).div_const 4
  refine (J.spatial_test_integral_tendsto w l r).congr' ?_
  filter_upwards [(((hl.add hw).eventually (Iio_mem_nhds hL)).and
    ((hr.sub hw).eventually (Ioi_mem_nhds hR))).filter_mono sourceLimitFilter_le_atTop]
    with n hn
  rw [finiteMeasure, innerJointFiniteMeasure, FiniteMeasure.toMeasure_mk,
    innerJointMeasure_restrict_spatial _ _ hn.1.le hn.2.le]

theorem niche_sub_eq_cosine_integral
    (hTarget : IsDownwardCap target) {l r : ℝ}
    (hl : l ∈ Icc a b) (hr : r ∈ Icc a b) (hlr : l ≤ r)
    (hL : horizontalLeft target + capWidth target / 4 < l)
    (hR : r < horizontalRight target - capWidth target / 4) :
    sweptNiche target (Real.pi / 2) r - sweptNiche target (Real.pi / 2) l =
      ∫ z in univ ×ˢ Ioc l r, -Real.cos z.1 ∂(J.measure : Measure Plane) := by
  refine tendsto_nhds_unique (f := fun n => ∫ z : Plane, -Real.cos z.1
    ∂innerJointMeasure (J.caps n) (dyadic (J.level n)) l r) ?_
    (J.local_test_integral_tendsto hTarget (-sourceCosineFunction) hL hR)
  simpa only [finiteBarrier_sub_eq_joint_cosine_integral _ _ hlr] using
    ((finiteBarrier_dyadic_tendsto J.hausdorff J.isCap hTarget J.level_tendsto
      (fun n => (J.selected n).inBox) (fun _ => hr) tendsto_const_nhds).sub
      (finiteBarrier_dyadic_tendsto J.hausdorff J.isCap hTarget J.level_tendsto
        (fun n => (J.selected n).inBox) (fun _ => hl) tendsto_const_nhds)).mono_left
      sourceLimitFilter_le_atTop

theorem horizontalProjection_restrict_Ioo_eq_volume_of_positive
    (hTarget : IsDownwardCap target) {l r : ℝ}
    (hbox : Ioo l r ⊆ Icc a b)
    (hmiddle : Ioo l r ⊆ Ioo (horizontalLeft target + capWidth target / 4)
      (horizontalRight target - capWidth target / 4))
    (hpositive : ∀ x ∈ Ioo l r, 0 < sweptNiche target (Real.pi / 2) x) :
    (J.horizontalProjection : Measure ℝ).restrict (Ioo l r) = volume.restrict (Ioo l r) := by
  -- On a compact subinterval the sine flux is the whole length, since the finite barriers are
  -- eventually positive there.
  have hIoc {x y : ℝ} (hxy : Icc x y ⊆ Ioo l r) :
      (J.horizontalProjection : Measure ℝ) (Ioc x y) = volume (Ioc x y) := by
    rcases lt_or_ge y x with h | h
    · simp [Ioc_eq_empty_of_le h.le]
    have hx := hxy (left_mem_Icc.2 h)
    have hy := hxy (right_mem_Icc.2 h)
    have hpos := eventually_finiteBarrier_pos_on_compact J.hausdorff J.isCap hTarget
      J.level_tendsto (fun n => (J.selected n).inBox) isCompact_Icc
      (fun z hz => hbox (hxy hz)) (fun z hz => hpositive z (hxy hz))
    have hconst : ∀ᶠ n in (sourceLimitFilter : Filter ℕ), y - x =
        ∫ z : Plane, Real.sin z.1 ∂innerJointMeasure (J.caps n) (dyadic (J.level n)) x y := by
      filter_upwards [hpos.filter_mono sourceLimitFilter_le_atTop] with n hn
      rw [integral_innerJointMeasure_sin _ _ h, finitePositiveLength, inter_eq_left.2 ?_,
        Real.volume_real_Ioc_of_le h]
      exact fun z hz => hn z (Ioc_subset_Icc_self hz)
    rw [← ofReal_measureReal (measure_ne_top _ _), Real.volume_Ioc,
      (J.horizontalProjection_real_eq_sine_integral measurableSet_Ioc).trans
        (tendsto_nhds_unique (J.local_test_integral_tendsto hTarget sourceSineFunction
          (hmiddle hx).1 (hmiddle hy).2) (tendsto_const_nhds.congr' hconst))]
  refine measure_restrict_Ioo_eq_of_closed_subintervals fun x y hxy =>
    Measure.ext_of_Ioc _ _ fun u v _ => ?_
  rw [Measure.restrict_apply measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc,
    Ioc_inter_Ioc]
  exact hIoc ((Icc_subset_Icc le_sup_right inf_le_right).trans hxy)

end SelectedJointSourceLimit
end AngularGrid
end AmbidextrousSofa
