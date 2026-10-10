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
    (J.measure : Measure Plane).map Prod.snd ≪ (volume : Measure ℝ) := by
  have hweight := (absolutelyContinuous_weightedFiniteMeasure J.measure
    sourceSineFunction.nnrealPart J.sinePart_ne_zero_ae).map measurable_snd
  exact hweight.trans (Measure.absolutelyContinuous_of_le J.horizontalProjection_le_volume)

theorem horizontalProjection_real_eq_sine_integral {E : Set ℝ} (hE : MeasurableSet E) :
    (J.horizontalProjection : Measure ℝ).real E =
      ∫ z in univ ×ˢ E, Real.sin z.1 ∂(J.measure : Measure Plane) := by
  rw [Measure.real, horizontalProjection, sourceHorizontalProjection_apply _ hE]
  change (weightedFiniteMeasure J.measure sourceSineFunction.nnrealPart : Measure Plane).real
    (univ ×ˢ E) = _
  rw [weightedFiniteMeasure_real_apply _ _ (MeasurableSet.univ.prod hE)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae J.ae_angle_mem_upper] with z hz
  change (Real.toNNReal (Real.sin z.1) : ℝ) = Real.sin z.1
  exact Real.coe_toNNReal _ (Real.sin_pos_of_pos_of_lt_pi hz.1 hz.2).le

theorem eventually_middle_contains
    (hTarget : IsDownwardCap target) {l r : ℝ}
    (hL : horizontalLeft target + capWidth target / 4 < l)
    (hR : r < horizontalRight target - capWidth target / 4) :
    ∀ᶠ n in atTop,
      horizontalLeft (J.caps n) + capWidth (J.caps n) / 4 < l ∧
        r < horizontalRight (J.caps n) - capWidth (J.caps n) / 4 := by
  have hl := J.hausdorff.horizontalLeft_tendsto (fun n => (J.isCap n).isCompact)
    (fun n => (J.isCap n).nonempty) hTarget.isCompact hTarget.nonempty
  have hr := J.hausdorff.horizontalRight_tendsto (fun n => (J.isCap n).isCompact)
    (fun n => (J.isCap n).nonempty) hTarget.isCompact hTarget.nonempty
  have hw := (J.hausdorff.capWidth_tendsto J.isCap hTarget).div_const 4
  exact ((hl.add hw).eventually (Iio_mem_nhds hL)).and
    ((hr.sub hw).eventually (Ioi_mem_nhds hR))

theorem eventually_restrict_spatial_eq
    (hTarget : IsDownwardCap target) {l r : ℝ}
    (hL : horizontalLeft target + capWidth target / 4 < l)
    (hR : r < horizontalRight target - capWidth target / 4) :
    ∀ᶠ n in atTop,
      (J.finiteMeasure n : Measure Plane).restrict (univ ×ˢ Ioc l r) =
        innerJointMeasure (J.caps n) (dyadic (J.level n)) l r := by
  filter_upwards [J.eventually_middle_contains hTarget hL hR] with n hn
  exact innerJointMeasure_restrict_spatial (J.caps n) (dyadic (J.level n)) hn.1.le hn.2.le

theorem local_test_integral_tendsto
    (hTarget : IsDownwardCap target) (w : Plane →ᵇ ℝ) {l r : ℝ}
    (hL : horizontalLeft target + capWidth target / 4 < l)
    (hR : r < horizontalRight target - capWidth target / 4) :
    Tendsto (fun n => ∫ z, w z ∂innerJointMeasure (J.caps n) (dyadic (J.level n)) l r)
      (sourceLimitFilter : Filter ℕ)
      (𝓝 (∫ z in univ ×ˢ Ioc l r, w z ∂(J.measure : Measure Plane))) := by
  apply (J.spatial_test_integral_tendsto w l r).congr'
  filter_upwards [(J.eventually_restrict_spatial_eq hTarget hL hR).filter_mono
    sourceLimitFilter_le_atTop] with n hn
  rw [hn]

theorem niche_sub_eq_cosine_integral
    (hTarget : IsDownwardCap target) {l r : ℝ}
    (hl : l ∈ Icc a b) (hr : r ∈ Icc a b) (hlr : l ≤ r)
    (hL : horizontalLeft target + capWidth target / 4 < l)
    (hR : r < horizontalRight target - capWidth target / 4) :
    sweptNiche target (Real.pi / 2) r - sweptNiche target (Real.pi / 2) l =
      ∫ z in univ ×ˢ Ioc l r, -Real.cos z.1 ∂(J.measure : Measure Plane) := by
  have hleft := finiteBarrier_dyadic_tendsto J.hausdorff J.isCap hTarget J.level_tendsto
    (fun n => (J.selected n).inBox) (fun _ => hl) tendsto_const_nhds
  have hright := finiteBarrier_dyadic_tendsto J.hausdorff J.isCap hTarget J.level_tendsto
    (fun n => (J.selected n).inBox) (fun _ => hr) tendsto_const_nhds
  have hgraph := (hright.sub hleft).mono_left sourceLimitFilter_le_atTop
  have hflux := J.local_test_integral_tendsto hTarget (-sourceCosineFunction) hL hR
  have heq (n : ℕ) := finiteBarrier_sub_eq_joint_cosine_integral
    (J.caps n) (dyadic (J.level n)) hlr
  have hgraph' : Tendsto
      (fun n => ∫ z : Plane, -Real.cos z.1
        ∂innerJointMeasure (J.caps n) (dyadic (J.level n)) l r)
      (sourceLimitFilter : Filter ℕ)
      (𝓝 (sweptNiche target (Real.pi / 2) r - sweptNiche target (Real.pi / 2) l)) := by
    simpa only [heq] using hgraph
  exact tendsto_nhds_unique hgraph' hflux

theorem sine_integral_eq_length_of_positive
    (hTarget : IsDownwardCap target) {l r : ℝ}
    (hl : l ∈ Icc a b) (hr : r ∈ Icc a b) (hlr : l ≤ r)
    (hL : horizontalLeft target + capWidth target / 4 < l)
    (hR : r < horizontalRight target - capWidth target / 4)
    (hpositive : ∀ x ∈ Icc l r, 0 < sweptNiche target (Real.pi / 2) x) :
    (∫ z in univ ×ˢ Ioc l r, Real.sin z.1 ∂(J.measure : Measure Plane)) = r - l := by
  have hpos := eventually_finiteBarrier_pos_on_compact J.hausdorff J.isCap hTarget
    J.level_tendsto (fun n => (J.selected n).inBox) isCompact_Icc
    (fun x hx => ⟨hl.1.trans hx.1, hx.2.trans hr.2⟩) hpositive
  have heq : ∀ᶠ n in atTop,
      (∫ z : Plane, Real.sin z.1
        ∂innerJointMeasure (J.caps n) (dyadic (J.level n)) l r) = r - l := by
    filter_upwards [hpos] with n hn
    rw [integral_innerJointMeasure_sin _ _ hlr]
    have hset : Ioc l r ∩ {x : ℝ | 0 < finiteBarrier (J.caps n)
        (normal (dyadic (J.level n))) (pairList (dyadic (J.level n))) none x} = Ioc l r :=
      inter_eq_left.mpr (fun x hx => hn x (Ioc_subset_Icc_self hx))
    rw [finitePositiveLength, hset, Real.volume_real_Ioc_of_le hlr]
  have hconst : Tendsto
      (fun n => ∫ z : Plane, Real.sin z.1
        ∂innerJointMeasure (J.caps n) (dyadic (J.level n)) l r)
      (sourceLimitFilter : Filter ℕ) (𝓝 (r - l)) :=
    tendsto_const_nhds.congr'
      (Filter.EventuallyEq.symm (Filter.Eventually.filter_mono sourceLimitFilter_le_atTop heq))
  exact tendsto_nhds_unique
    (J.local_test_integral_tendsto hTarget sourceSineFunction hL hR) hconst

theorem horizontalProjection_Ioc_eq_volume_of_positive
    (hTarget : IsDownwardCap target) {l r : ℝ}
    (hl : l ∈ Icc a b) (hr : r ∈ Icc a b) (hlr : l ≤ r)
    (hL : horizontalLeft target + capWidth target / 4 < l)
    (hR : r < horizontalRight target - capWidth target / 4)
    (hpositive : ∀ x ∈ Icc l r, 0 < sweptNiche target (Real.pi / 2) x) :
    (J.horizontalProjection : Measure ℝ) (Ioc l r) = volume (Ioc l r) := by
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) measure_Ioc_lt_top.ne).mp
  change (J.horizontalProjection : Measure ℝ).real (Ioc l r) = volume.real (Ioc l r)
  rw [J.horizontalProjection_real_eq_sine_integral measurableSet_Ioc,
    J.sine_integral_eq_length_of_positive hTarget hl hr hlr hL hR hpositive,
    Real.volume_real_Ioc_of_le hlr]

theorem horizontalProjection_restrict_Ioc_eq_volume_of_positive
    (hTarget : IsDownwardCap target) {l r : ℝ}
    (hl : l ∈ Icc a b) (hr : r ∈ Icc a b)
    (hL : horizontalLeft target + capWidth target / 4 < l)
    (hR : r < horizontalRight target - capWidth target / 4)
    (hpositive : ∀ x ∈ Icc l r, 0 < sweptNiche target (Real.pi / 2) x) :
    (J.horizontalProjection : Measure ℝ).restrict (Ioc l r) = volume.restrict (Ioc l r) := by
  apply Measure.ext_of_Ioc
  intro x y _hxy
  rw [Measure.restrict_apply measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc]
  have hinter : Ioc x y ∩ Ioc l r = Ioc (max x l) (min y r) := by
    ext z
    simp only [mem_inter_iff, mem_Ioc, max_lt_iff, le_min_iff]
    tauto
  rw [hinter]
  by_cases hspan : max x l ≤ min y r
  · have hsub : Icc (max x l) (min y r) ⊆ Icc l r :=
      fun z hz => ⟨(le_max_right _ _).trans hz.1, hz.2.trans (min_le_right _ _)⟩
    exact J.horizontalProjection_Ioc_eq_volume_of_positive hTarget
      ⟨hl.1.trans (le_max_right _ _),
        (hspan.trans (min_le_right _ _)).trans hr.2⟩
      ⟨hl.1.trans ((le_max_right _ _).trans hspan), (min_le_right _ _).trans hr.2⟩
      hspan (hL.trans_le (le_max_right _ _)) ((min_le_right _ _).trans_lt hR)
      (fun z hz => hpositive z (hsub hz))
  · simp only [Ioc_eq_empty_of_le (le_of_not_ge hspan), measure_empty]

theorem horizontalProjection_restrict_Ioo_eq_volume_of_positive
    (hTarget : IsDownwardCap target) {l r : ℝ}
    (hbox : Ioo l r ⊆ Icc a b)
    (hmiddle : Ioo l r ⊆ Ioo (horizontalLeft target + capWidth target / 4)
      (horizontalRight target - capWidth target / 4))
    (hpositive : ∀ x ∈ Ioo l r, 0 < sweptNiche target (Real.pi / 2) x) :
    (J.horizontalProjection : Measure ℝ).restrict (Ioo l r) = volume.restrict (Ioo l r) := by
  apply measure_restrict_Ioo_eq_of_closed_subintervals
  intro x y hxy
  by_cases hspan : x ≤ y
  · have hx := hxy (left_mem_Icc.mpr hspan)
    have hy := hxy (right_mem_Icc.mpr hspan)
    exact J.horizontalProjection_restrict_Ioc_eq_volume_of_positive hTarget
      (hbox hx) (hbox hy) (hmiddle hx).1 (hmiddle hy).2
      (fun z hz => hpositive z (hxy hz))
  · simp only [Ioc_eq_empty_of_le (le_of_not_ge hspan), Measure.restrict_empty]

end SelectedJointSourceLimit
end AngularGrid
end AmbidextrousSofa
