module

public import AmbidextrousSofa.Analysis.FiniteGraphFlux
public import Mathlib.MeasureTheory.Measure.FiniteMeasure

@[expose] public section

/-!
# The literal joint measure of finite inner sources

Each selected finite source retains both its normal angle and its
horizontal position. Its spatial measure is horizontal Lebesgue measure
on the selected source set, divided by the positive vertical component
of the unit normal. Thus its total mass is precisely the previously
defined source length.

The joint measure has the prescribed angular marginal, commutes with
restriction to a horizontal interval, and its sine and negative cosine
fluxes are the horizontal positive length and the vertical increment
of the finite graph. No limiting graph occupation or contact phase is
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
    IsFiniteMeasure (innerSpatialMeasure U grid l r j) :=
  ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top <| (Measure.restrict_apply_univ _).trans_lt <|
    (measure_mono inter_subset_left).trans_lt measure_Ioc_lt_top⟩

/-- Here the two coordinates are the normal angle and the horizontal
position; this is a source measure on their product, not on the cap. -/
def innerJointMeasure (U : Set Plane) (grid : Finset QuarterAngle)
    (l r : ℝ) : Measure Plane := by
  classical
  exact ∑ j : SourceIndex grid,
    (innerSpatialMeasure U grid l r j).map (fun x : ℝ => (fullAngle grid j, x))

instance innerJointMeasure_isFinite (U : Set Plane) (grid : Finset QuarterAngle)
    (l r : ℝ) : IsFiniteMeasure (innerJointMeasure U grid l r) := by
  unfold innerJointMeasure; infer_instance

def innerJointFiniteMeasure (U : Set Plane) (grid : Finset QuarterAngle)
    (l r : ℝ) : FiniteMeasure Plane :=
  ⟨innerJointMeasure U grid l r, inferInstance⟩

theorem innerSpatialMeasure_real_univ (U : Set Plane) (grid : Finset QuarterAngle)
    {l r : ℝ} (hlr : l ≤ r) (j : SourceIndex grid) :
    (innerSpatialMeasure U grid l r j).real univ = innerSourceMassOn U grid l r j := by
  rw [innerSpatialMeasure, measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal
    (one_div_pos.2 (normal_snd_pos grid j)).le, measureReal_restrict_apply_univ,
    innerSourceMassOn_eq_div U grid hlr]
  exact one_div_mul_eq_div _ _

theorem innerJointMeasure_apply (U : Set Plane) (grid : Finset QuarterAngle)
    (l r : ℝ) {E : Set Plane} (hE : MeasurableSet E) :
    innerJointMeasure U grid l r E =
      ∑ j : SourceIndex grid, ENNReal.ofReal (1 / (normal grid j).2) *
        volume ((fun x : ℝ => (fullAngle grid j, x)) ⁻¹' E ∩
          (Ioc l r ∩ innerSourceSet U grid j)) := by
  rw [innerJointMeasure, Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Measure.map_apply measurable_prodMk_left hE, innerSpatialMeasure, Measure.smul_apply,
    smul_eq_mul, Measure.restrict_apply (hE.preimage measurable_prodMk_left)]

/-- The angular marginal is the actual selected source mass, retaining
all atoms of the finite angular grid. -/
theorem innerJointMeasure_angular_mass (U : Set Plane) (grid : Finset QuarterAngle)
    {l r : ℝ} (hlr : l ≤ r) {E : Set ℝ} (hE : MeasurableSet E) :
    (innerJointMeasure U grid l r).real (E ×ˢ univ) =
      innerAngularMassOn U grid E l r := by
  classical
  rw [Measure.real, innerJointMeasure, Measure.finsetSum_apply,
    ENNReal.toReal_sum fun j _ => measure_ne_top _ _, innerAngularMassOn, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Measure.map_apply measurable_prodMk_left (hE.prod .univ), mk_preimage_prod_right_eq_if]
  split_ifs
  exacts [innerSpatialMeasure_real_univ U grid hlr j, by simp]

/-- Spatial localization is literal restriction of the same joint
measure; it does not select a new angular or spatial subsequence. -/
theorem innerJointMeasure_restrict_spatial (U : Set Plane) (grid : Finset QuarterAngle)
    (L R l r : ℝ) :
    (innerJointMeasure U grid L R).restrict (univ ×ˢ Ioc l r) =
      innerJointMeasure U grid (max L l) (min R r) := by
  ext E hE
  rw [Measure.restrict_apply hE, innerJointMeasure_apply U grid L R
    (hE.inter (MeasurableSet.univ.prod measurableSet_Ioc)), innerJointMeasure_apply U grid _ _ hE]
  refine Finset.sum_congr rfl fun j _ => congrArg _ (congrArg _ (ext fun x => ?_))
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and, mem_Ioc, max_lt_iff,
    le_min_iff]
  tauto

/-- Any measurable property enjoyed by every literal finite source
holds almost everywhere for the joint measure. -/
theorem innerJointMeasure_compl_eq_zero_of_source
    (U : Set Plane) (grid : Finset QuarterAngle) (l r : ℝ)
    {E : Set Plane} (hE : MeasurableSet E)
    (hsource : ∀ j : SourceIndex grid, ∀ x ∈ Ioc l r,
      x ∈ innerSourceSet U grid j → (fullAngle grid j, x) ∈ E) :
    innerJointMeasure U grid l r Eᶜ = 0 := by
  rw [innerJointMeasure_apply U grid l r hE.compl]
  exact Finset.sum_eq_zero fun j _ => mul_eq_zero_of_right _ <|
    measure_mono_null (fun x hx => (hx.1 (hsource j x hx.2.1 hx.2.2)).elim) measure_empty

theorem innerJointMeasure_compl_rectangle_eq_zero
    (U : Set Plane) (grid : Finset QuarterAngle)
    {L l r R : ℝ} (hLl : L ≤ l) (hrR : r ≤ R) :
    innerJointMeasure U grid l r (Icc (0 : ℝ) Real.pi ×ˢ Icc L R)ᶜ = 0 :=
  innerJointMeasure_compl_eq_zero_of_source U grid l r (measurableSet_Icc.prod measurableSet_Icc)
    fun j _ hx _ => ⟨Ioo_subset_Icc_self (fullAngle_mem grid j), hLl.trans hx.1.le, hx.2.trans hrR⟩

theorem integral_innerJointMeasure_angle (U : Set Plane) (grid : Finset QuarterAngle)
    {l r : ℝ} (hlr : l ≤ r) {w : ℝ → ℝ} (hw : Measurable w) :
    (∫ z : Plane, w z.1 ∂innerJointMeasure U grid l r) =
      ∑ j : SourceIndex grid, w (fullAngle grid j) * innerSourceMassOn U grid l r j := by
  have hm : Measurable fun z : Plane => w z.1 := by fun_prop
  rw [innerJointMeasure, integral_finsetSum_measure fun j _ => ?_]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_map measurable_prodMk_left.aemeasurable hm.aestronglyMeasurable]
    simp [innerSpatialMeasure_real_univ U grid hlr, mul_comm]
  · exact (integrable_map_measure hm.aestronglyMeasurable measurable_prodMk_left.aemeasurable).2
      (integrable_const (w (fullAngle grid j)))

/-- The sine-weighted source measure has exactly the positive horizontal
length, including finite zero-height ties. -/
theorem integral_innerJointMeasure_sin (U : Set Plane) (grid : Finset QuarterAngle)
    {l r : ℝ} (hlr : l ≤ r) :
    (∫ z : Plane, Real.sin z.1 ∂innerJointMeasure U grid l r) =
      finitePositiveLength U (normal grid) (pairList grid) none l r := by
  rw [integral_innerJointMeasure_angle U grid hlr Real.continuous_sin.measurable,
    finitePositiveLength_eq_sum U (normal grid) (pairList grid) none
      (wallSlopes_injective grid) hlr]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [innerSourceMassOn_eq_div U grid hlr, show Real.sin (fullAngle grid j) = (normal grid j).2 from
    (congrArg Prod.snd (normal_eq_unitNormal grid j)).symm]
  exact mul_div_cancel₀ _ (normal_snd_pos grid j).ne'

/-- The vertical graph increment is the negative cosine flux of the joint source measure. -/
theorem finiteBarrier_sub_eq_joint_cosine_integral
    (U : Set Plane) (grid : Finset QuarterAngle) {l r : ℝ} (hlr : l ≤ r) :
    finiteBarrier U (normal grid) (pairList grid) none r -
        finiteBarrier U (normal grid) (pairList grid) none l =
      ∫ z : Plane, -Real.cos z.1 ∂innerJointMeasure U grid l r := by
  have h := finiteBarrier_projection_eq_sources U grid hlr (Real.pi / 2)
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.sin_sub_pi_div_two, zero_mul, one_mul,
    zero_add] at h
  rw [h, integral_innerJointMeasure_angle U grid hlr (w := fun θ => -Real.cos θ) (by fun_prop)]

/-- On the middle window of a cap in `[-R, R] × [0, 1]`, the dyadic joint source measure has
mass at most `(4R + 12)π` and lives in `[0, π] × [-R, R]`. -/
theorem innerJointMeasure_middle_bounds
    {U : Set Plane} (hU : IsDownwardCap U) {R : ℝ} (hR : 0 ≤ R)
    (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1) (level : ℕ) :
    (innerJointMeasure U (dyadic level) (horizontalLeft U + capWidth U / 4)
      (horizontalRight U - capWidth U / 4)).real univ ≤ (4 * R + 12) * Real.pi ∧
    innerJointMeasure U (dyadic level) (horizontalLeft U + capWidth U / 4)
      (horizontalRight U - capWidth U / 4) (Icc (0 : ℝ) Real.pi ×ˢ Icc (-R) R)ᶜ = 0 := by
  obtain ⟨p, hp, hpl⟩ := horizontalLeft_mem hU.nonempty hU.isCompact
  obtain ⟨q, hq, hqr⟩ := horizontalRight_mem hU.nonempty hU.isCompact
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  refine ⟨?_, innerJointMeasure_compl_rectangle_eq_zero U _ ?_ ?_⟩
  · rw [← univ_prod_univ, innerJointMeasure_angular_mass U _ (by unfold capWidth; linarith) .univ]
    simp only [innerAngularMassOn, mem_univ, Finset.filter_true]
    exact sum_innerSourceMass_dyadic_le hU hR hbox level
  all_goals unfold capWidth; linarith [(hbox hp).1.1, (hbox hq).1.2]

end AngularGrid
end AmbidextrousSofa
