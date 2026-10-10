import AmbidextrousSofa.Analysis.JointSourceContacts
import AmbidextrousSofa.Measure.RealRadonNikodym
import Mathlib.MeasureTheory.Group.Measure

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

theorem volume_restrict_regular_eq_upper (m : ℝ) :
    (volume : Measure ℝ).restrict (regularCurvatureDomain m) =
      volume.restrict (Ioo (0 : ℝ) Real.pi) := by
  apply Measure.restrict_congr_set
  filter_upwards [volume.ae_ne (Real.pi / 2), volume.ae_ne (affineNormalAngle m)] with t ht htm
  simp only [regularCurvatureDomain, mem_sdiff, mem_insert_iff, mem_singleton_iff,
    ht, htm, or_self, not_false_eq_true, and_true]

theorem ae_regularCornerDomain_of_mem_quarter (m : ℝ) :
    ∀ᵐ t : ℝ ∂volume, t ∈ Ioo (0 : ℝ) (Real.pi / 2) → t ∈ regularCornerDomain m := by
  filter_upwards [volume.ae_ne (affineNormalAngle m),
    volume.ae_ne (affineNormalAngle m - Real.pi / 2)] with t ht htm
  intro hti
  refine ⟨hti, ?_, ?_⟩
  · refine ⟨⟨hti.1, by linarith only [hti.2, Real.pi_pos]⟩, ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨hti.2.ne, ht⟩
  · refine ⟨⟨by linarith only [hti.1, Real.pi_pos], by linarith only [hti.2]⟩, ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨by linarith only [hti.1], fun heq => htm (by linarith only [heq])⟩

namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

theorem ae_angle_ne (θ : ℝ) : ∀ᵐ z ∂(J.measure : Measure Plane), z.1 ≠ θ := by
  simpa only [mem_prod, mem_singleton_iff, mem_univ, and_true] using
    measure_eq_zero_iff_ae_notMem.mp (J.angular_fiber_eq_zero θ)

theorem ae_angle_mem_regular (m : ℝ) :
    ∀ᵐ z ∂(J.measure : Measure Plane), z.1 ∈ regularCurvatureDomain m := by
  filter_upwards [J.ae_angle_mem_upper, J.ae_angle_ne (Real.pi / 2),
    J.ae_angle_ne (affineNormalAngle m)] with z hz htop haff
  exact ⟨hz, by simpa only [mem_insert_iff, mem_singleton_iff, not_or] using And.intro htop haff⟩

theorem angularMeasure_restrict_regular_eq_self (m : ℝ) :
    J.angularMeasure.restrict (regularCurvatureDomain m) = J.angularMeasure := by
  apply Measure.restrict_eq_self_of_ae_mem
  exact (ae_map_iff measurable_fst.aemeasurable (measurableSet_regularCurvatureDomain m)).mpr
    (J.ae_angle_mem_regular m)

section ActualDensity

variable (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
  {m c : ℝ} {ρ : ℝ → ℝ}
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
    capRoof target x = m * x + c)
  (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
  (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)
  (heq : (upperCurvature target).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

theorem angularMeasure_eq_density :
    J.angularMeasure = (volume.restrict (Ioo (0 : ℝ) Real.pi)).withDensity
      (fun t => ENNReal.ofReal (ρ t)) := by
  have h := J.angularMeasure_restrict_regular_eq_density hTarget hheight haffine
    hTargetBox hleft hright heq
  rwa [J.angularMeasure_restrict_regular_eq_self,
    volume_restrict_regular_eq_upper] at h

theorem angularMeasure_absolutelyContinuous : J.angularMeasure ≪ volume := by
  rw [J.angularMeasure_eq_density hTarget hheight haffine hTargetBox hleft hright heq]
  exact (withDensity_absolutelyContinuous _ _).trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

theorem shifted_angle_absolutelyContinuous (d : ℝ) :
    (J.measure : Measure Plane).map (fun z => z.1 - d) ≪ (volume : Measure ℝ) := by
  have h := (J.angularMeasure_absolutelyContinuous hTarget hheight haffine hTargetBox
    hleft hright heq).map (measurable_id.sub_const d)
  rw [map_sub_right_eq_self] at h
  simpa only [angularMeasure, Measure.map_map (measurable_id.sub_const d) measurable_fst,
    Function.comp_apply] using h

theorem ae_shifted_angle_regularCorner (d : ℝ) :
    ∀ᵐ z ∂(J.measure : Measure Plane),
      z.1 - d ∈ Ioo (0 : ℝ) (Real.pi / 2) → z.1 - d ∈ regularCornerDomain m := by
  have h := (J.shifted_angle_absolutelyContinuous hTarget hheight haffine hTargetBox
    hleft hright heq d).ae_le (ae_regularCornerDomain_of_mem_quarter m)
  exact ae_of_ae_map (measurable_fst.sub_const d).aemeasurable h

end ActualDensity
end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
