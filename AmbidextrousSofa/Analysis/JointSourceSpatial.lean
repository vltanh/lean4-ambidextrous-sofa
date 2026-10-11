module

public import AmbidextrousSofa.Analysis.JointSourceMarginal
public import AmbidextrousSofa.Measure.WeightedFiniteMeasure

@[expose] public section

/-!
# Spatial projection of the common source measure

The positive sine weight turns actual source arclength into horizontal
graph length. The finite identity is retained on every spatial interval,
including its exact intersection with the middle window. Weak convergence
then gives horizontal domination by Lebesgue measure and rules out spatial
atoms of the joint source measure.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped BoundedContinuousFunction
open scoped Topology

namespace AmbidextrousSofa

def sourceSineFunction : Plane →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun z => Real.sin z.1, Real.continuous_sin.comp continuous_fst⟩ 2 (by
      intro z w
      show dist (Real.sin z.1) (Real.sin w.1) ≤ 2
      rw [Real.dist_eq]
      apply abs_le.mpr
      constructor <;> linarith only [Real.neg_one_le_sin z.1, Real.sin_le_one z.1,
        Real.neg_one_le_sin w.1, Real.sin_le_one w.1])

def sourceCosineFunction : Plane →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun z => Real.cos z.1, Real.continuous_cos.comp continuous_fst⟩ 2 (by
      intro z w
      show dist (Real.cos z.1) (Real.cos w.1) ≤ 2
      rw [Real.dist_eq]
      apply abs_le.mpr
      constructor <;> linarith only [Real.neg_one_le_cos z.1, Real.cos_le_one z.1,
        Real.neg_one_le_cos w.1, Real.cos_le_one w.1])

def sourceHorizontalProjection (μ : FiniteMeasure Plane) : FiniteMeasure ℝ :=
  (weightedFiniteMeasure μ sourceSineFunction.nnrealPart).map Prod.snd

theorem sourceHorizontalProjection_apply (μ : FiniteMeasure Plane)
    {E : Set ℝ} (hE : MeasurableSet E) :
    (sourceHorizontalProjection μ : Measure ℝ) E =
      (weightedFiniteMeasure μ sourceSineFunction.nnrealPart : Measure Plane) (univ ×ˢ E) := by
  rw [sourceHorizontalProjection, FiniteMeasure.toMeasure_map,
    Measure.map_apply measurable_snd hE, univ_prod]

theorem sourceHorizontalProjection_tendsto
    {ι : Type*} {L : Filter ι} {μ : FiniteMeasure Plane} {ν : ι → FiniteMeasure Plane}
    (hlim : Tendsto ν L (𝓝 μ)) :
    Tendsto (fun i => sourceHorizontalProjection (ν i)) L (𝓝 (sourceHorizontalProjection μ)) :=
  FiniteMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (weightedFiniteMeasure_tendsto hlim sourceSineFunction.nnrealPart) continuous_snd

namespace AngularGrid

open FinitePolygon

theorem innerJointMeasure_restrict_spatial_inter
    (U : Set Plane) (grid : Finset QuarterAngle) (L R l r : ℝ) :
    (innerJointMeasure U grid L R).restrict (univ ×ˢ Ioc l r) =
      innerJointMeasure U grid (max L l) (min R r) := by
  ext E hE
  rw [Measure.restrict_apply hE, innerJointMeasure_apply U grid L R
    (hE.inter (MeasurableSet.univ.prod measurableSet_Ioc)), innerJointMeasure_apply U grid _ _ hE]
  refine Finset.sum_congr rfl fun j _ => congrArg _ (congrArg _ (ext fun x => ?_))
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and, mem_Ioc, max_lt_iff,
    le_min_iff]
  tauto

theorem innerJointMeasure_sinePart_ae
    (U : Set Plane) (grid : Finset QuarterAngle) (l r : ℝ) :
    (fun z : Plane => (sourceSineFunction.nnrealPart z : ℝ)) =ᵐ[innerJointMeasure U grid l r]
      fun z => Real.sin z.1 := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp
    (innerJointMeasure_compl_rectangle_eq_zero U grid le_rfl le_rfl)] with z hz
  exact Real.coe_toNNReal _ (Real.sin_nonneg_of_mem_Icc (not_not.1 hz).1)

theorem finite_horizontalProjection_Ioc_real_le
    (U : Set Plane) (grid : Finset QuarterAngle) (L R : ℝ) {l r : ℝ} (hlr : l ≤ r) :
    (sourceHorizontalProjection (innerJointFiniteMeasure U grid L R) : Measure ℝ).real (Ioc l r) ≤
      r - l := by
  rw [sourceHorizontalProjection, FiniteMeasure.toMeasure_map,
    map_measureReal_apply measurable_snd measurableSet_Ioc, ← univ_prod,
    weightedFiniteMeasure_real_apply _ _ (MeasurableSet.univ.prod measurableSet_Ioc)]
  change (∫ z in univ ×ˢ Ioc l r, (sourceSineFunction.nnrealPart z : ℝ)
    ∂innerJointMeasure U grid L R) ≤ _
  rw [integral_congr_ae (ae_restrict_of_ae (innerJointMeasure_sinePart_ae U grid L R)),
    innerJointMeasure_restrict_spatial_inter]
  rcases le_or_gt (max L l) (min R r) with hspan | hspan
  · rw [integral_innerJointMeasure_sin U grid hspan, finitePositiveLength,
      ← Real.volume_real_Ioc_of_le hlr]
    exact measureReal_mono (inter_subset_left.trans
      (Ioc_subset_Ioc (le_max_right _ _) (min_le_right _ _))) measure_Ioc_lt_top.ne
  · simp [innerJointMeasure, innerSpatialMeasure, Ioc_eq_empty_of_le hspan.le, hlr]

namespace SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

def horizontalProjection : FiniteMeasure ℝ := sourceHorizontalProjection J.measure

theorem horizontalProjection_Ioo_le (l r : ℝ) :
    (J.horizontalProjection : Measure ℝ) (Ioo l r) ≤ volume (Ioo l r) := by
  rcases le_or_gt l r with hlr | hlr
  · rw [Real.volume_Ioo, ← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal <| finiteMeasure_real_open_le_of_tendsto_bound
      (sourceHorizontalProjection_tendsto J.converges) isOpen_Ioo (sub_nonneg.2 hlr)
      tendsto_const_nhds <| .of_forall fun n => (measureReal_mono Ioo_subset_Ioc_self).trans
        (finite_horizontalProjection_Ioc_real_le _ _ _ _ hlr)
  · simp [Ioo_eq_empty_of_le hlr.le]

theorem horizontalProjection_le_volume : (J.horizontalProjection : Measure ℝ) ≤ volume := by
  have hnull :
      (J.horizontalProjection : Measure ℝ) (Ioo (-(|a| + |b| + 2)) (|a| + |b| + 2))ᶜ = 0 := by
    rw [horizontalProjection, sourceHorizontalProjection_apply _ measurableSet_Ioo.compl]
    refine weightedFiniteMeasure_absolutelyContinuous _ _ (measure_mono_null ?_ J.outside_box)
    exact fun z hz hrect => hz.2 ⟨by linarith [hrect.2.1], by linarith [hrect.2.2]⟩
  refine (MovingSofaOptimality.inj_measure_le_of_Ioo fun l r _ => ?_).trans
    (Measure.restrict_le_self (s := Ioo (-(|a| + |b| + 2)) (|a| + |b| + 2)))
  rw [Measure.restrict_apply measurableSet_Ioo, ← measure_inter_conull hnull, Ioo_inter_Ioo]
  exact J.horizontalProjection_Ioo_le _ _

theorem ae_angle_mem_upper :
    ∀ᵐ z ∂(J.measure : Measure Plane), z.1 ∈ Ioo (0 : ℝ) Real.pi := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp J.outside_box,
    measure_eq_zero_iff_ae_notMem.mp (J.angular_fiber_eq_zero 0),
    measure_eq_zero_iff_ae_notMem.mp (J.angular_fiber_eq_zero Real.pi)] with z hz h0 hπ
  exact ⟨(not_not.1 hz).1.1.lt_of_ne fun h => h0 ⟨h.symm, mem_univ _⟩,
    (not_not.1 hz).1.2.lt_of_ne fun h => hπ ⟨h, mem_univ _⟩⟩

theorem sinePart_ne_zero_ae :
    ∀ᵐ z ∂(J.measure : Measure Plane), sourceSineFunction.nnrealPart z ≠ 0 := by
  filter_upwards [J.ae_angle_mem_upper] with z hz
  exact (Real.toNNReal_pos.mpr (Real.sin_pos_of_pos_of_lt_pi hz.1 hz.2)).ne'

theorem spatial_fiber_eq_zero (x : ℝ) :
    (J.measure : Measure Plane) (univ ×ˢ {x}) = 0 := by
  refine absolutelyContinuous_weightedFiniteMeasure J.measure sourceSineFunction.nnrealPart
    J.sinePart_ne_zero_ae ?_
  rw [← sourceHorizontalProjection_apply _ (measurableSet_singleton x)]
  exact Measure.absolutelyContinuous_of_le J.horizontalProjection_le_volume (measure_singleton x)

theorem spatial_test_integral_tendsto (w : Plane →ᵇ ℝ) (l r : ℝ) :
    Tendsto (fun n => ∫ z in univ ×ˢ Ioc l r, w z ∂(J.finiteMeasure n : Measure Plane))
      (sourceLimitFilter : Filter ℕ)
      (𝓝 (∫ z in univ ×ˢ Ioc l r, w z ∂(J.measure : Measure Plane))) := by
  refine finiteMeasure_tendsto_setIntegral_boundedContinuous J.converges w
    (MeasurableSet.univ.prod measurableSet_Ioc) ?_
  rcases lt_or_ge l r with hlr | hlr
  · rw [frontier_univ_prod_eq, frontier_Ioc hlr, insert_eq, prod_union]
    exact measure_union_null (J.spatial_fiber_eq_zero l) (J.spatial_fiber_eq_zero r)
  · simp [Ioc_eq_empty_of_le hlr]

end SelectedJointSourceLimit
end AngularGrid
end AmbidextrousSofa
