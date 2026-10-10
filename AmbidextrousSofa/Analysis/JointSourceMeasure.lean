import AmbidextrousSofa.Analysis.FiniteGraphFlux
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# The literal joint measure of finite inner sources

Each selected finite source retains both its normal angle and its
horizontal position. Its spatial measure is horizontal Lebesgue measure
on the selected source set, divided by the positive vertical component
of the unit normal. Thus its total mass is precisely the previously
defined source length.

The joint measure has the prescribed angular marginal, commutes with
restriction to a smaller horizontal interval, and satisfies both exact
graph flux identities. No limiting graph occupation or contact phase is
assumed in this construction.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa
namespace AngularGrid

open FinitePolygon

/-- The actual arclength measure of one selected source, before tagging
its angle. -/
def innerSpatialMeasure (U : Set Plane) (grid : Finset QuarterAngle)
    (l r : ℝ) (j : SourceIndex grid) : Measure ℝ :=
  ENNReal.ofReal (1 / (normal grid j).2) •
    volume.restrict (Ioc l r ∩ innerSourceSet U grid j)

instance innerSpatialMeasure_isFinite (U : Set Plane) (grid : Finset QuarterAngle)
    (l r : ℝ) (j : SourceIndex grid) :
    IsFiniteMeasure (innerSpatialMeasure U grid l r j) := by
  constructor
  rw [innerSpatialMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply MeasurableSet.univ, univ_inter]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    ((measure_mono inter_subset_left).trans_lt measure_Ioc_lt_top)

/-- Here the two coordinates are the normal angle and the horizontal
position; this is a source measure on their product, not on the cap. -/
def innerJointMeasure (U : Set Plane) (grid : Finset QuarterAngle)
    (l r : ℝ) : Measure Plane := by
  classical
  exact ∑ j : SourceIndex grid,
    (innerSpatialMeasure U grid l r j).map (fun x : ℝ => (fullAngle grid j, x))

instance innerJointMeasure_isFinite (U : Set Plane) (grid : Finset QuarterAngle)
    (l r : ℝ) : IsFiniteMeasure (innerJointMeasure U grid l r) := by
  classical
  unfold innerJointMeasure
  infer_instance

def innerJointFiniteMeasure (U : Set Plane) (grid : Finset QuarterAngle)
    (l r : ℝ) : FiniteMeasure Plane :=
  ⟨innerJointMeasure U grid l r, inferInstance⟩

@[simp]
theorem innerJointFiniteMeasure_toMeasure (U : Set Plane) (grid : Finset QuarterAngle)
    (l r : ℝ) :
    (innerJointFiniteMeasure U grid l r : Measure Plane) =
      innerJointMeasure U grid l r := rfl

theorem innerSpatialMeasure_real_univ (U : Set Plane) (grid : Finset QuarterAngle)
    {l r : ℝ} (hlr : l ≤ r) (j : SourceIndex grid) :
    (innerSpatialMeasure U grid l r j).real univ = innerSourceMassOn U grid l r j := by
  have hny : 0 ≤ 1 / (normal grid j).2 :=
    (one_div_pos.mpr (normal_snd_pos grid j)).le
  rw [innerSpatialMeasure, measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal hny,
    measureReal_restrict_apply_univ, innerSourceMassOn_eq_div U grid hlr]
  change (1 / (normal grid j).2) * volume.real (Ioc l r ∩ innerSourceSet U grid j) =
    volume.real (Ioc l r ∩ innerSourceSet U grid j) / (normal grid j).2
  ring

theorem innerJointMeasure_apply (U : Set Plane) (grid : Finset QuarterAngle)
    (l r : ℝ) {E : Set Plane} (hE : MeasurableSet E) :
    innerJointMeasure U grid l r E =
      ∑ j : SourceIndex grid, ENNReal.ofReal (1 / (normal grid j).2) *
        volume ((fun x : ℝ => (fullAngle grid j, x)) ⁻¹' E ∩
          (Ioc l r ∩ innerSourceSet U grid j)) := by
  classical
  rw [innerJointMeasure, Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Measure.map_apply (measurable_const.prodMk measurable_id) hE,
    innerSpatialMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply (hE.preimage (measurable_const.prodMk measurable_id))]

theorem innerJointMeasure_prod (U : Set Plane) (grid : Finset QuarterAngle)
    (l r : ℝ) {E S : Set ℝ} (hE : MeasurableSet E) (hS : MeasurableSet S) :
    innerJointMeasure U grid l r (E ×ˢ S) =
      ∑ j : SourceIndex grid,
        if fullAngle grid j ∈ E then innerSpatialMeasure U grid l r j S else 0 := by
  classical
  rw [innerJointMeasure, Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Measure.map_apply (measurable_const.prodMk measurable_id) (hE.prod hS)]
  have hpre : (fun x : ℝ => (fullAngle grid j, x)) ⁻¹' (E ×ˢ S) =
      if fullAngle grid j ∈ E then S else ∅ := by
    ext x
    by_cases hj : fullAngle grid j ∈ E <;> simp [hj]
  rw [hpre]
  split_ifs <;> simp

/-- The angular marginal is the actual selected source mass, retaining
all atoms of the finite angular grid. -/
theorem innerJointMeasure_angular_mass (U : Set Plane) (grid : Finset QuarterAngle)
    {l r : ℝ} (hlr : l ≤ r) {E : Set ℝ} (hE : MeasurableSet E) :
    (innerJointMeasure U grid l r).real (E ×ˢ univ) =
      innerAngularMassOn U grid E l r := by
  classical
  rw [Measure.real, innerJointMeasure_prod U grid l r hE MeasurableSet.univ,
    ENNReal.toReal_sum (fun j _ => by split_ifs <;> simp)]
  simp only [innerAngularMassOn, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · exact innerSpatialMeasure_real_univ U grid hlr j
  · rfl

theorem innerJointMeasure_real_univ (U : Set Plane) (grid : Finset QuarterAngle)
    {l r : ℝ} (hlr : l ≤ r) :
    (innerJointMeasure U grid l r).real univ =
      ∑ j : SourceIndex grid, innerSourceMassOn U grid l r j := by
  classical
  simpa only [univ_prod_univ, innerAngularMassOn, mem_univ, Finset.filter_true]
    using innerJointMeasure_angular_mass U grid hlr (E := univ) MeasurableSet.univ

/-- Spatial localization is literal restriction of the same joint
measure; it does not select a new angular or spatial subsequence. -/
theorem innerJointMeasure_restrict_spatial (U : Set Plane) (grid : Finset QuarterAngle)
    {L l r R : ℝ} (hLl : L ≤ l) (hrR : r ≤ R) :
    (innerJointMeasure U grid L R).restrict (univ ×ˢ Ioc l r) =
      innerJointMeasure U grid l r := by
  classical
  apply Measure.ext
  intro E hE
  rw [Measure.restrict_apply hE,
    innerJointMeasure_apply U grid L R
      (hE.inter (MeasurableSet.univ.prod measurableSet_Ioc)),
    innerJointMeasure_apply U grid l r hE]
  apply Finset.sum_congr rfl
  intro j _
  have hset : (fun x : ℝ => (fullAngle grid j, x)) ⁻¹' (E ∩ (univ ×ˢ Ioc l r)) ∩
        (Ioc L R ∩ innerSourceSet U grid j) =
      (fun x : ℝ => (fullAngle grid j, x)) ⁻¹' E ∩
        (Ioc l r ∩ innerSourceSet U grid j) := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and]
    constructor
    · rintro ⟨⟨hxE, hx⟩, _, hs⟩
      exact ⟨hxE, hx, hs⟩
    · rintro ⟨hxE, hx, hs⟩
      exact ⟨⟨hxE, hx⟩, ⟨hLl.trans_lt hx.1, hx.2.trans hrR⟩, hs⟩
  rw [hset]

/-- Any measurable property enjoyed by every literal finite source
holds almost everywhere for the joint measure. -/
theorem innerJointMeasure_compl_eq_zero_of_source
    (U : Set Plane) (grid : Finset QuarterAngle) (l r : ℝ)
    {E : Set Plane} (hE : MeasurableSet E)
    (hsource : ∀ j : SourceIndex grid, ∀ x ∈ Ioc l r,
      x ∈ innerSourceSet U grid j → (fullAngle grid j, x) ∈ E) :
    innerJointMeasure U grid l r Eᶜ = 0 := by
  classical
  rw [innerJointMeasure_apply U grid l r hE.compl]
  apply Finset.sum_eq_zero
  intro j _
  have hempty : (fun x : ℝ => (fullAngle grid j, x)) ⁻¹' Eᶜ ∩
      (Ioc l r ∩ innerSourceSet U grid j) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx.1 (hsource j x hx.2.1 hx.2.2)
  rw [hempty, measure_empty, mul_zero]

theorem innerJointMeasure_compl_rectangle_eq_zero
    (U : Set Plane) (grid : Finset QuarterAngle)
    {L l r R : ℝ} (hLl : L ≤ l) (hrR : r ≤ R) :
    innerJointMeasure U grid l r (Icc (0 : ℝ) Real.pi ×ˢ Icc L R)ᶜ = 0 := by
  apply innerJointMeasure_compl_eq_zero_of_source U grid l r
    (measurableSet_Icc.prod measurableSet_Icc)
  intro j x hx _
  exact ⟨⟨(fullAngle_mem grid j).1.le, (fullAngle_mem grid j).2.le⟩,
    hLl.trans hx.1.le, hx.2.trans hrR⟩

theorem integrable_innerJointMeasure_angle (U : Set Plane) (grid : Finset QuarterAngle)
    (l r : ℝ) {w : ℝ → ℝ} (hw : Measurable w) :
    Integrable (fun z : Plane => w z.1) (innerJointMeasure U grid l r) := by
  classical
  unfold innerJointMeasure
  apply integrable_finsetSum_measure.mpr
  intro j _
  apply (integrable_map_measure (hw.comp measurable_fst).aestronglyMeasurable
    (measurable_const.prodMk measurable_id).aemeasurable).mpr
  simpa only [Function.comp_apply] using
    (integrable_const (w (fullAngle grid j)) :
      Integrable (fun _ : ℝ => w (fullAngle grid j)) (innerSpatialMeasure U grid l r j))

theorem integral_innerJointMeasure_angle (U : Set Plane) (grid : Finset QuarterAngle)
    {l r : ℝ} (hlr : l ≤ r) {w : ℝ → ℝ} (hw : Measurable w) :
    (∫ z : Plane, w z.1 ∂innerJointMeasure U grid l r) =
      ∑ j : SourceIndex grid, w (fullAngle grid j) * innerSourceMassOn U grid l r j := by
  classical
  have hi := integrable_innerJointMeasure_angle U grid l r hw
  rw [innerJointMeasure] at hi ⊢
  rw [integral_finsetSum_measure (integrable_finsetSum_measure.mp hi)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_map_of_stronglyMeasurable (measurable_const.prodMk measurable_id)
    (hw.comp measurable_fst).stronglyMeasurable]
  change (∫ _ : ℝ, w (fullAngle grid j) ∂innerSpatialMeasure U grid l r j) = _
  rw [integral_const, smul_eq_mul, innerSpatialMeasure_real_univ U grid hlr]
  ring

/-- The sine-weighted source measure has exactly the positive horizontal
length, including finite zero-height ties. -/
theorem integral_innerJointMeasure_sin (U : Set Plane) (grid : Finset QuarterAngle)
    {l r : ℝ} (hlr : l ≤ r) :
    (∫ z : Plane, Real.sin z.1 ∂innerJointMeasure U grid l r) =
      finitePositiveLength U (normal grid) (pairList grid) none l r := by
  rw [integral_innerJointMeasure_angle U grid hlr Real.continuous_sin.measurable,
    finitePositiveLength_eq_sum U (normal grid) (pairList grid) none
      (wallSlopes_injective grid) hlr]
  apply Finset.sum_congr rfl
  intro j _
  rw [innerSourceMassOn_eq_div U grid hlr]
  have hny : (normal grid j).2 = Real.sin (fullAngle grid j) :=
    congrArg Prod.snd (normal_eq_unitNormal grid j)
  rw [← hny]
  field_simp [(normal_snd_pos grid j).ne'] <;> ring

/-- Both oriented graph increments use the same joint source measure.
The floor contribution is retained explicitly. -/
theorem finiteBarrier_projection_eq_joint_integral
    (U : Set Plane) (grid : Finset QuarterAngle) {l r : ℝ} (hlr : l ≤ r) (t : ℝ) :
    Real.cos t * (r - l) + Real.sin t *
        (finiteBarrier U (normal grid) (pairList grid) none r -
          finiteBarrier U (normal grid) (pairList grid) none l) =
      Real.cos t *
        (barrierExpr (pairList grid) none).sourceMass (wallSlope (normal grid))
          (barrierIntercept (normal grid) (fun i => support U (normal grid i))) l r none +
      ∫ z : Plane, Real.sin (z.1 - t) ∂innerJointMeasure U grid l r := by
  rw [integral_innerJointMeasure_angle U grid hlr
    (Real.continuous_sin.measurable.comp (measurable_id.sub_const t))]
  exact finiteBarrier_projection_eq_sources U grid hlr t

theorem innerJointMeasure_middle_mass_dyadic_le
    {U : Set Plane} (hU : IsDownwardCap U) {R : ℝ} (hR : 0 ≤ R)
    (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1) (level : ℕ) :
    (innerJointMeasure U (dyadic level)
      (horizontalLeft U + capWidth U / 4)
      (horizontalRight U - capWidth U / 4)).real univ ≤ (4 * R + 12) * Real.pi := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  rw [innerJointMeasure_real_univ U (dyadic level)
    (show horizontalLeft U + capWidth U / 4 ≤ horizontalRight U - capWidth U / 4 by
      unfold capWidth
      linarith)]
  exact sum_innerSourceMass_dyadic_le hU hR hbox level

theorem innerJointMeasure_middle_compl_box_eq_zero
    {U : Set Plane} (hU : IsDownwardCap U) {R : ℝ}
    (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1) (grid : Finset QuarterAngle) :
    innerJointMeasure U grid
      (horizontalLeft U + capWidth U / 4)
      (horizontalRight U - capWidth U / 4)
      (Icc (0 : ℝ) Real.pi ×ˢ Icc (-R) R)ᶜ = 0 := by
  obtain ⟨p, hp, hpl⟩ := horizontalLeft_mem hU.nonempty hU.isCompact
  obtain ⟨q, hq, hqr⟩ := horizontalRight_mem hU.nonempty hU.isCompact
  have hleft : -R ≤ horizontalLeft U := by
    rw [← hpl]
    exact (hbox hp).1.1
  have hright : horizontalRight U ≤ R := by
    rw [← hqr]
    exact (hbox hq).1.2
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  apply innerJointMeasure_compl_rectangle_eq_zero U grid
  · unfold capWidth
    linarith
  · unfold capWidth
    linarith

end AngularGrid
end AmbidextrousSofa
