module

public import AmbidextrousSofa.Analysis.JointSourceContacts
public import AmbidextrousSofa.Measure.RealRadonNikodym
public import Mathlib.MeasureTheory.Group.Measure

@[expose] public section

/-!
# Full angular density of the joint source limit

The common source measure has no mass at any exceptional normal. Its
already identified regular angular marginal therefore extends across
the two removed normals as a density on the open upper semicircle.
All translated angular marginals are absolutely continuous with respect
to Lebesgue measure. This transfers the actual almost everywhere support
calculus to each literal source branch.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem ae_regularCornerDomain_of_mem_quarter (m : ℝ) :
    ∀ᵐ t : ℝ ∂volume, t ∈ Ioo (0 : ℝ) (Real.pi / 2) → t ∈ regularCornerDomain m := by
  filter_upwards [volume.ae_ne (affineNormalAngle m),
    volume.ae_ne (affineNormalAngle m - Real.pi / 2)] with t ht htm hti
  refine ⟨hti, ⟨⟨hti.1, by linarith [hti.2, Real.pi_pos]⟩, ?_⟩,
    ⟨⟨by linarith [hti.1, Real.pi_pos], by linarith [hti.2]⟩, ?_⟩⟩ <;>
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
  · exact ⟨hti.2.ne, ht⟩
  · exact ⟨by linarith [hti.1], fun h => htm (by linarith)⟩

namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

theorem ae_angle_ne (θ : ℝ) : ∀ᵐ z ∂(J.measure : Measure Plane), z.1 ≠ θ := by
  simpa only [mem_prod, mem_singleton_iff, mem_univ, and_true] using
    measure_eq_zero_iff_ae_notMem.mp (J.angular_fiber_eq_zero θ)

section ActualDensity

variable (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
  {m c : ℝ} {ρ : ℝ → ℝ}
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
    capRoof target x = m * x + c)
  (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
  (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)
  (heq : (upperCurvature target).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

include hTarget hheight haffine hTargetBox hleft hright heq in
theorem angularMeasure_eq_density :
    J.angularMeasure = (volume.restrict (Ioo (0 : ℝ) Real.pi)).withDensity
      (fun t => ENNReal.ofReal (ρ t)) := by
  have hself : J.angularMeasure.restrict (regularCurvatureDomain m) = J.angularMeasure := by
    refine Measure.restrict_eq_self_of_ae_mem ((ae_map_iff measurable_fst.aemeasurable
      (measurableSet_regularCurvatureDomain m)).mpr ?_)
    filter_upwards [J.ae_angle_mem_upper, J.ae_angle_ne (Real.pi / 2),
      J.ae_angle_ne (affineNormalAngle m)] with z hz htop haff
    exact ⟨hz, by simp [htop, haff]⟩
  have hvol : (volume : Measure ℝ).restrict (regularCurvatureDomain m) =
      volume.restrict (Ioo (0 : ℝ) Real.pi) :=
    Measure.restrict_congr_set (sdiff_null_ae_eq_self ((Set.toFinite _).measure_zero _))
  rw [← hself, ← hvol]
  exact J.angularMeasure_restrict_regular_eq_density hTarget hheight haffine hTargetBox hleft
    hright heq

include hTarget hheight haffine hTargetBox hleft hright heq in
theorem shifted_angle_absolutelyContinuous (d : ℝ) :
    (J.measure : Measure Plane).map (fun z => z.1 - d) ≪ (volume : Measure ℝ) := by
  have h : J.angularMeasure ≪ volume := by
    rw [J.angularMeasure_eq_density hTarget hheight haffine hTargetBox hleft hright heq]
    exact (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict
  have h' := h.map (measurable_sub_const' d)
  rw [map_sub_right_eq_self volume d] at h'
  simpa only [angularMeasure, Measure.map_map (measurable_sub_const' d) measurable_fst,
    Function.comp_def] using h'

include hTarget hheight haffine hTargetBox hleft hright heq in
theorem ae_shifted_angle_regularCorner (d : ℝ) :
    ∀ᵐ z ∂(J.measure : Measure Plane),
      z.1 - d ∈ Ioo (0 : ℝ) (Real.pi / 2) → z.1 - d ∈ regularCornerDomain m :=
  ae_of_ae_map (measurable_fst.sub_const d).aemeasurable
    ((J.shifted_angle_absolutelyContinuous hTarget hheight haffine hTargetBox hleft hright heq
      d).ae_le (ae_regularCornerDomain_of_mem_quarter m))

end ActualDensity
end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
