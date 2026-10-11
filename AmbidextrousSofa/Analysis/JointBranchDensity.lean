module

public import AmbidextrousSofa.Analysis.JointSourceBranches

@[expose] public section

/-!
# Angular densities of the four common-source branches

The sum of the two first branch densities is the actual first curvature
density. Translating the two companion branches back by a quarter turn
gives the actual companion density. These statements identify the
Radon--Nikodym representatives of the literal restrictions, rather than
introducing independent occupation weights.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem ae_realRnDensity_eq_on_of_withDensity_restrict
    {μ : Measure ℝ} {S : Set ℝ} {ρ : ℝ → ℝ}
    (hS : MeasurableSet S) (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t)
    (hμ : μ = (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t))) :
    ∀ᵐ t ∂volume.restrict S, realRnDensity μ volume t = ρ t := by
  have hd := ae_realRnDensity_eq_of_withDensity (μ := μ) (ν := volume) (hρ.indicator hS)
    (indicator_nonneg fun t _ => hρ0 t) (by
      rw [hμ, ← withDensity_indicator hS]
      exact congrArg _ (indicator_comp_of_zero ENNReal.ofReal_zero))
  filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae hd] with t ht heq
  simpa only [indicator_of_mem ht] using heq

theorem map_second_quarter_density {ρ : ℝ → ℝ} (hρ : Measurable ρ) :
    ((volume.restrict (Ioo (Real.pi / 2) Real.pi)).withDensity
      (fun t => ENNReal.ofReal (ρ t))).map (fun t => t - Real.pi / 2) =
        (volume.restrict (Ioo (0 : ℝ) (Real.pi / 2))).withDensity
          (fun t => ENNReal.ofReal (ρ (t + Real.pi / 2))) := by
  have hpre : (fun t : ℝ => t - Real.pi / 2) ⁻¹' Ioo 0 (Real.pi / 2) =
      Ioo (Real.pi / 2) Real.pi := by
    rw [preimage_sub_const_Ioo, zero_add, add_halves]
  have hv : (volume.restrict (Ioo (Real.pi / 2) Real.pi)).map
      (fun t => t - Real.pi / 2) = volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [← hpre, ← Measure.restrict_map (measurable_sub_const' _) measurableSet_Ioo,
      map_sub_right_eq_self]
  simpa only [Function.comp_apply, sub_add_cancel, hv] using map_withDensity_comp
    (volume.restrict (Ioo (Real.pi / 2) Real.pi)) (measurable_sub_const' (Real.pi / 2))
    (hρ.comp (measurable_add_const (Real.pi / 2))).ennreal_ofReal

namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

section ActualDensity

variable (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
  {m c : ℝ} {ρ : ℝ → ℝ}
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
    capRoof target x = m * x + c)
  (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
  (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t)
  (heq : (upperCurvature target).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

include hTarget hheight haffine hTargetBox hleft hright hρ hρ0 heq in
theorem ae_first_source_density_sum
    (hpositive : ∀ᵐ z ∂(J.measure : Measure Plane),
      0 < sweptNiche target (Real.pi / 2) z.2) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      J.sourceBranchDensity (firstTangentSource target) 0 t +
        J.sourceBranchDensity (firstCornerSource target) 0 t = ρ t := by
  have hsum : J.sourceBranchAngular (firstTangentSource target) 0 +
      J.sourceBranchAngular (firstCornerSource target) 0 =
        (volume.restrict (Ioo (0 : ℝ) (Real.pi / 2))).withDensity
          (fun t => ENNReal.ofReal (ρ t)) := by
    have h : J.sourceBranchAngular (firstTangentSource target) 0 +
        J.sourceBranchAngular (firstCornerSource target) 0 =
          J.angularMeasure.restrict (Ioo (0 : ℝ) (Real.pi / 2)) := by
      rw [sourceBranchAngular, sourceBranchAngular, ← Measure.map_add _ _
        (measurable_fst.sub_const 0), J.first_source_partition hTarget.isCap hpositive,
        angularMeasure, Measure.restrict_map measurable_fst measurableSet_Ioo]
      simp only [sub_zero]
      rfl
    rw [h, J.angularMeasure_eq_density hTarget hheight haffine hTargetBox hleft hright heq,
      restrict_withDensity measurableSet_Ioo, Measure.restrict_restrict_of_subset
        (Ioo_subset_Ioo le_rfl (by linarith [Real.pi_pos]))]
  filter_upwards [ae_realRnDensity_eq_on_of_withDensity_restrict measurableSet_Ioo hρ hρ0 hsum,
    ae_restrict_of_ae (ae_realRnDensity_add (J.sourceBranchAngular (firstTangentSource target) 0)
      (J.sourceBranchAngular (firstCornerSource target) 0) volume)] with t ht hs
  exact hs.symm.trans ht

include hTarget hheight haffine hTargetBox hleft hright hρ hρ0 heq in
theorem ae_second_source_density_sum
    (hpositive : ∀ᵐ z ∂(J.measure : Measure Plane),
      0 < sweptNiche target (Real.pi / 2) z.2) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      J.sourceBranchDensity (secondTangentSource target) (Real.pi / 2) t +
        J.sourceBranchDensity (secondCornerSource target) (Real.pi / 2) t =
          ρ (t + Real.pi / 2) := by
  have hsum : J.sourceBranchAngular (secondTangentSource target) (Real.pi / 2) +
      J.sourceBranchAngular (secondCornerSource target) (Real.pi / 2) =
        (volume.restrict (Ioo (0 : ℝ) (Real.pi / 2))).withDensity
          (fun t => ENNReal.ofReal (ρ (t + Real.pi / 2))) := by
    have h : J.sourceBranchAngular (secondTangentSource target) (Real.pi / 2) +
        J.sourceBranchAngular (secondCornerSource target) (Real.pi / 2) =
          (J.angularMeasure.restrict (Ioo (Real.pi / 2) Real.pi)).map
            (fun t => t - Real.pi / 2) := by
      rw [sourceBranchAngular, sourceBranchAngular, ← Measure.map_add _ _
        (measurable_fst.sub_const _), J.second_source_partition hTarget.isCap hpositive,
        angularMeasure, Measure.restrict_map measurable_fst measurableSet_Ioo,
        Measure.map_map (measurable_sub_const' _) measurable_fst]
      rfl
    rw [h, J.angularMeasure_eq_density hTarget hheight haffine hTargetBox hleft hright heq,
      restrict_withDensity measurableSet_Ioo, Measure.restrict_restrict_of_subset
        (Ioo_subset_Ioo (by positivity : (0 : ℝ) ≤ Real.pi / 2) le_rfl),
      map_second_quarter_density hρ]
  filter_upwards [ae_realRnDensity_eq_on_of_withDensity_restrict measurableSet_Ioo
    (hρ.comp (measurable_add_const _)) (fun t => hρ0 _) hsum,
    ae_restrict_of_ae (ae_realRnDensity_add
      (J.sourceBranchAngular (secondTangentSource target) (Real.pi / 2))
      (J.sourceBranchAngular (secondCornerSource target) (Real.pi / 2)) volume)] with t ht hs
  exact hs.symm.trans ht

include hTarget hheight haffine hTargetBox hleft hright heq in
theorem ae_sourceBranchDensity_eq_zero_on
    {S : Set Plane} {d : ℝ} {E : Set ℝ} (hE : MeasurableSet E)
    (hzero : ∀ᵐ z ∂J.sourceBranchMeasure S, z.1 - d ∉ E) :
    ∀ᵐ t ∂volume, t ∈ E → J.sourceBranchDensity S d t = 0 := by
  have hz : J.sourceBranchAngular S d E = 0 := (Measure.map_apply
    (measurable_fst.sub_const d) hE).trans (measure_eq_zero_iff_ae_notMem.mpr hzero)
  rw [J.sourceBranchAngular_eq_density hTarget hheight haffine hTargetBox hleft hright heq,
    withDensity_apply _ hE,
    lintegral_eq_zero_iff (J.measurable_sourceBranchDensity S d).ennreal_ofReal] at hz
  exact (ae_restrict_iff' hE).mp (hz.mono fun t ht =>
    le_antisymm (ENNReal.ofReal_eq_zero.mp ht) (J.sourceBranchDensity_nonneg S d t))

end ActualDensity
end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
