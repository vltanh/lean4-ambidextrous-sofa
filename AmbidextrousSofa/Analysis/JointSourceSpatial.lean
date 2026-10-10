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
  classical
  apply Measure.ext
  intro E hE
  rw [Measure.restrict_apply hE,
    innerJointMeasure_apply U grid L R
      (hE.inter (MeasurableSet.univ.prod measurableSet_Ioc)),
    innerJointMeasure_apply U grid (max L l) (min R r) hE]
  apply Finset.sum_congr rfl
  intro j _
  have hset : (fun x : ℝ => (fullAngle grid j, x)) ⁻¹' (E ∩ (univ ×ˢ Ioc l r)) ∩
        (Ioc L R ∩ innerSourceSet U grid j) =
      (fun x : ℝ => (fullAngle grid j, x)) ⁻¹' E ∩
        (Ioc (max L l) (min R r) ∩ innerSourceSet U grid j) := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and,
      mem_Ioc, max_lt_iff, le_min_iff]
    tauto
  rw [hset]

theorem innerJointMeasure_eq_zero_of_le
    (U : Set Plane) (grid : Finset QuarterAngle) {l r : ℝ} (hrl : r ≤ l) :
    innerJointMeasure U grid l r = 0 := by
  classical
  simp only [innerJointMeasure, innerSpatialMeasure, Ioc_eq_empty_of_le hrl, empty_inter,
    Measure.restrict_empty, smul_zero, Measure.map_zero, Finset.sum_const_zero]

theorem innerJointMeasure_sinePart_ae
    (U : Set Plane) (grid : Finset QuarterAngle) (l r : ℝ) :
    (fun z : Plane => (sourceSineFunction.nnrealPart z : ℝ)) =ᵐ[innerJointMeasure U grid l r]
      fun z => Real.sin z.1 := by
  have hmem : ∀ᵐ z ∂innerJointMeasure U grid l r,
      z ∈ Icc (0 : ℝ) Real.pi ×ˢ Icc l r := by
    rw [ae_iff]
    exact innerJointMeasure_compl_rectangle_eq_zero U grid le_rfl le_rfl
  filter_upwards [hmem] with z hz
  change (Real.toNNReal (Real.sin z.1) : ℝ) = Real.sin z.1
  exact Real.coe_toNNReal _ (Real.sin_nonneg_of_mem_Icc hz.1)

theorem finite_horizontalProjection_Ioc_real
    (U : Set Plane) (grid : Finset QuarterAngle) (L R l r : ℝ) :
    (sourceHorizontalProjection (innerJointFiniteMeasure U grid L R) : Measure ℝ).real (Ioc l r) =
      finitePositiveLength U (normal grid) (pairList grid) none (max L l) (min R r) := by
  rw [sourceHorizontalProjection, FiniteMeasure.toMeasure_map,
    map_measureReal_apply measurable_snd measurableSet_Ioc, ← univ_prod,
    weightedFiniteMeasure_real_apply _ _ (MeasurableSet.univ.prod measurableSet_Ioc)]
  change (∫ z in univ ×ˢ Ioc l r, (sourceSineFunction.nnrealPart z : ℝ)
    ∂innerJointMeasure U grid L R) = _
  rw [integral_congr_ae (ae_restrict_of_ae (innerJointMeasure_sinePart_ae U grid L R)),
    innerJointMeasure_restrict_spatial_inter]
  by_cases hspan : max L l ≤ min R r
  · exact integral_innerJointMeasure_sin U grid hspan
  · rw [innerJointMeasure_eq_zero_of_le U grid (le_of_not_ge hspan), integral_zero_measure]
    simp only [finitePositiveLength, Ioc_eq_empty_of_le (le_of_not_ge hspan), empty_inter,
      measureReal_empty]

theorem finite_horizontalProjection_Ioc_real_le
    (U : Set Plane) (grid : Finset QuarterAngle) (L R : ℝ) {l r : ℝ} (hlr : l ≤ r) :
    (sourceHorizontalProjection (innerJointFiniteMeasure U grid L R) : Measure ℝ).real (Ioc l r) ≤
      r - l := by
  rw [finite_horizontalProjection_Ioc_real]
  unfold finitePositiveLength
  calc
    _ ≤ volume.real (Ioc l r) := by
      apply measureReal_mono
      intro x hx
      exact ⟨(le_max_right _ _).trans_lt hx.1.1, hx.1.2.trans (min_le_right _ _)⟩
    _ = r - l := Real.volume_real_Ioc_of_le hlr

namespace SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

def horizontalProjection : FiniteMeasure ℝ := sourceHorizontalProjection J.measure

theorem horizontalProjection_converges :
    Tendsto (fun n => sourceHorizontalProjection (J.finiteMeasure n))
      (sourceLimitFilter : Filter ℕ) (𝓝 J.horizontalProjection) :=
  sourceHorizontalProjection_tendsto J.converges

theorem horizontalProjection_Ioo_real_le {l r : ℝ} (hlr : l ≤ r) :
    (J.horizontalProjection : Measure ℝ).real (Ioo l r) ≤ r - l := by
  apply finiteMeasure_real_open_le_of_tendsto_bound J.horizontalProjection_converges
    isOpen_Ioo (sub_nonneg.mpr hlr) tendsto_const_nhds
  apply Eventually.of_forall
  intro n
  exact (measureReal_mono Ioo_subset_Ioc_self).trans
    (finite_horizontalProjection_Ioc_real_le (J.caps n) (dyadic (J.level n))
      (horizontalLeft (J.caps n) + capWidth (J.caps n) / 4)
      (horizontalRight (J.caps n) - capWidth (J.caps n) / 4) hlr)

theorem horizontalProjection_Ioo_le (l r : ℝ) :
    (J.horizontalProjection : Measure ℝ) (Ioo l r) ≤ volume (Ioo l r) := by
  by_cases hlr : l ≤ r
  · calc
      _ = ENNReal.ofReal ((J.horizontalProjection : Measure ℝ).real (Ioo l r)) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (r - l) := ENNReal.ofReal_le_ofReal (J.horizontalProjection_Ioo_real_le hlr)
      _ = volume (Ioo l r) := Real.volume_Ioo.symm
  · simp only [Ioo_eq_empty_of_le (le_of_not_ge hlr), measure_empty, le_rfl]

theorem horizontalProjection_le_volume : (J.horizontalProjection : Measure ℝ) ≤ volume := by
  let R := |a| + |b| + 1
  let S : Set ℝ := Ioo (-(R + 1)) (R + 1)
  have hnull : (J.horizontalProjection : Measure ℝ) Sᶜ = 0 := by
    rw [horizontalProjection, sourceHorizontalProjection_apply _ measurableSet_Ioo.compl]
    apply weightedFiniteMeasure_absolutelyContinuous J.measure sourceSineFunction.nnrealPart
    apply measure_mono_null _ J.outside_box
    intro z hz hrect
    apply hz.2
    change -(R + 1) < z.2 ∧ z.2 < R + 1
    dsimp only [R]
    constructor <;> linarith only [hrect.2.1, hrect.2.2]
  have hrest : (J.horizontalProjection : Measure ℝ).restrict S =
      (J.horizontalProjection : Measure ℝ) := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    exact hnull
  have hdom : (J.horizontalProjection : Measure ℝ) ≤ volume.restrict S := by
    letI : IsFiniteMeasure ((volume : Measure ℝ).restrict S) :=
      isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
    apply MovingSofaOptimality.inj_measure_le_of_Ioo
    intro l r _hlr
    have hinter : Ioo l r ∩ S = Ioo (max l (-(R + 1))) (min r (R + 1)) := by
      ext x
      simp only [S, mem_inter_iff, mem_Ioo, max_lt_iff, lt_min_iff]
      tauto
    calc
      _ = ((J.horizontalProjection : Measure ℝ).restrict S) (Ioo l r) := by rw [hrest]
      _ = (J.horizontalProjection : Measure ℝ)
          (Ioo (max l (-(R + 1))) (min r (R + 1))) := by
        rw [Measure.restrict_apply measurableSet_Ioo, hinter]
      _ ≤ volume (Ioo (max l (-(R + 1))) (min r (R + 1))) := J.horizontalProjection_Ioo_le _ _
      _ = volume.restrict S (Ioo l r) := by rw [Measure.restrict_apply measurableSet_Ioo, hinter]
  exact hdom.trans Measure.restrict_le_self

instance horizontalProjection_nullSingletonClass :
    NullSingletonClass (J.horizontalProjection : Measure ℝ) where
  measure_singleton x :=
    Measure.absolutelyContinuous_of_le J.horizontalProjection_le_volume (measure_singleton x)

theorem ae_angle_mem_upper :
    ∀ᵐ z ∂(J.measure : Measure Plane), z.1 ∈ Ioo (0 : ℝ) Real.pi := by
  have hbox : ∀ᵐ z ∂(J.measure : Measure Plane),
      z ∈ Icc (0 : ℝ) Real.pi ×ˢ Icc (-(|a| + |b| + 1)) (|a| + |b| + 1) := by
    rw [ae_iff]
    exact J.outside_box
  have hzero : ∀ᵐ z ∂(J.measure : Measure Plane), z.1 ≠ 0 := by
    simpa only [mem_prod, mem_singleton_iff, mem_univ, and_true] using
      measure_eq_zero_iff_ae_notMem.mp (J.angular_fiber_eq_zero 0)
  have hpi : ∀ᵐ z ∂(J.measure : Measure Plane), z.1 ≠ Real.pi := by
    simpa only [mem_prod, mem_singleton_iff, mem_univ, and_true] using
      measure_eq_zero_iff_ae_notMem.mp (J.angular_fiber_eq_zero Real.pi)
  filter_upwards [hbox, hzero, hpi] with z hz h0 hπ
  exact ⟨lt_of_le_of_ne hz.1.1 h0.symm, lt_of_le_of_ne hz.1.2 hπ⟩

theorem sinePart_ne_zero_ae :
    ∀ᵐ z ∂(J.measure : Measure Plane), sourceSineFunction.nnrealPart z ≠ 0 := by
  filter_upwards [J.ae_angle_mem_upper] with z hz
  change Real.toNNReal (Real.sin z.1) ≠ 0
  exact (Real.toNNReal_pos.mpr (Real.sin_pos_of_pos_of_lt_pi hz.1 hz.2)).ne'

theorem spatial_fiber_eq_zero (x : ℝ) :
    (J.measure : Measure Plane) (univ ×ˢ {x}) = 0 := by
  have hweighted :
      (weightedFiniteMeasure J.measure sourceSineFunction.nnrealPart : Measure Plane)
        (univ ×ˢ {x}) = 0 := by
    rw [← sourceHorizontalProjection_apply _ (measurableSet_singleton x)]
    exact measure_singleton x
  exact absolutelyContinuous_weightedFiniteMeasure J.measure sourceSineFunction.nnrealPart
    J.sinePart_ne_zero_ae hweighted

theorem spatial_Ioc_frontier_eq_zero (l r : ℝ) :
    (J.measure : Measure Plane) (frontier ((univ : Set ℝ) ×ˢ Ioc l r)) = 0 := by
  by_cases hlr : l < r
  · have hprod : (univ : Set ℝ) ×ˢ ({l, r} : Set ℝ) =
        (univ ×ˢ {l}) ∪ (univ ×ˢ {r}) := by
      ext z
      simp only [mem_prod, mem_insert_iff, mem_singleton_iff, mem_univ, true_and, mem_union]
    rw [frontier_univ_prod_eq, frontier_Ioc hlr, hprod]
    exact measure_union_null (J.spatial_fiber_eq_zero l) (J.spatial_fiber_eq_zero r)
  · simp only [Ioc_eq_empty_of_le (le_of_not_gt hlr), prod_empty, frontier_empty, measure_empty]

theorem spatial_test_integral_tendsto (w : Plane →ᵇ ℝ) (l r : ℝ) :
    Tendsto (fun n => ∫ z in univ ×ˢ Ioc l r, w z ∂(J.finiteMeasure n : Measure Plane))
      (sourceLimitFilter : Filter ℕ)
      (𝓝 (∫ z in univ ×ˢ Ioc l r, w z ∂(J.measure : Measure Plane))) :=
  finiteMeasure_tendsto_setIntegral_boundedContinuous J.converges w
    (MeasurableSet.univ.prod measurableSet_Ioc) (J.spatial_Ioc_frontier_eq_zero l r)

end SelectedJointSourceLimit
end AngularGrid
end AmbidextrousSofa
