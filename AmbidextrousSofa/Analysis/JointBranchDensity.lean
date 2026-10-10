import AmbidextrousSofa.Analysis.JointSourceBranches

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
  have hind : (fun t => ENNReal.ofReal (S.indicator ρ t)) =
      S.indicator (fun t => ENNReal.ofReal (ρ t)) := by
    funext t
    by_cases ht : t ∈ S
    · simp only [indicator_of_mem ht]
    · simp only [indicator_of_not_mem ht, ENNReal.ofReal_zero]
  have hμ' : μ = volume.withDensity (fun t => ENNReal.ofReal (S.indicator ρ t)) := by
    rw [hind, withDensity_indicator hS]
    exact hμ
  have h0 : ∀ t, 0 ≤ S.indicator ρ t := by
    intro t
    by_cases ht : t ∈ S
    · simpa only [indicator_of_mem ht] using hρ0 t
    · simp only [indicator_of_not_mem ht, le_refl]
  have hd := ae_realRnDensity_eq_of_withDensity (hρ.indicator hS) h0 hμ'
  filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae hd] with t ht heq
  simpa only [indicator_of_mem ht] using heq

theorem map_second_quarter_density {ρ : ℝ → ℝ} (hρ : Measurable ρ) :
    ((volume.restrict (Ioo (Real.pi / 2) Real.pi)).withDensity
      (fun t => ENNReal.ofReal (ρ t))).map (fun t => t - Real.pi / 2) =
        (volume.restrict (Ioo (0 : ℝ) (Real.pi / 2))).withDensity
          (fun t => ENNReal.ofReal (ρ (t + Real.pi / 2))) := by
  have hpre : (fun t : ℝ => t - Real.pi / 2) ⁻¹' Ioo (0 : ℝ) (Real.pi / 2) =
      Ioo (Real.pi / 2) Real.pi := by
    ext t
    simp only [mem_preimage, mem_Ioo]
    constructor <;> intro ht <;> constructor <;> linarith only [ht.1, ht.2]
  have hv : (volume.restrict (Ioo (Real.pi / 2) Real.pi)).map
      (fun t => t - Real.pi / 2) = volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [← hpre, ← Measure.restrict_map (measurable_id.sub_const _) measurableSet_Ioo,
      map_sub_right_eq_self]
  have hmap := map_withDensity_comp
    (volume.restrict (Ioo (Real.pi / 2) Real.pi))
    (measurable_id.sub_const (Real.pi / 2))
    (hρ.comp (measurable_id.add_const (Real.pi / 2))).ennreal_ofReal
  simpa only [sub_add_cancel, hv] using hmap

namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

theorem first_branchAngular_sum (hTarget : IsDownwardCap target)
    (hpositive : ∀ᵐ z ∂(J.measure : Measure Plane),
      0 < sweptNiche target (Real.pi / 2) z.2) :
    J.sourceBranchAngular (firstTangentSource target) 0 +
      J.sourceBranchAngular (firstCornerSource target) 0 =
        J.angularMeasure.restrict (Ioo (0 : ℝ) (Real.pi / 2)) := by
  change (J.sourceBranchMeasure (firstTangentSource target)).map (fun z => z.1 - 0) +
    (J.sourceBranchMeasure (firstCornerSource target)).map (fun z => z.1 - 0) = _
  rw [← Measure.map_add _ _ (measurable_fst.sub_const 0),
    J.first_source_partition hTarget hpositive]
  simpa only [sourceBranchMeasure, firstSourceSlice, sub_zero, angularMeasure] using
    (Measure.restrict_map (μ := (J.measure : Measure Plane)) measurable_fst
      (s := Ioo (0 : ℝ) (Real.pi / 2)) measurableSet_Ioo).symm

theorem second_branchAngular_sum (hTarget : IsDownwardCap target)
    (hpositive : ∀ᵐ z ∂(J.measure : Measure Plane),
      0 < sweptNiche target (Real.pi / 2) z.2) :
    J.sourceBranchAngular (secondTangentSource target) (Real.pi / 2) +
      J.sourceBranchAngular (secondCornerSource target) (Real.pi / 2) =
        (J.angularMeasure.restrict (Ioo (Real.pi / 2) Real.pi)).map
          (fun t => t - Real.pi / 2) := by
  change (J.sourceBranchMeasure (secondTangentSource target)).map (fun z => z.1 - Real.pi / 2) +
    (J.sourceBranchMeasure (secondCornerSource target)).map (fun z => z.1 - Real.pi / 2) = _
  rw [← Measure.map_add _ _ (measurable_fst.sub_const _),
    J.second_source_partition hTarget hpositive]
  rw [angularMeasure, Measure.restrict_map measurable_fst measurableSet_Ioo,
    Measure.map_map (measurable_id.sub_const _) measurable_fst]
  rfl

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

theorem first_branchAngular_sum_eq_density
    (hpositive : ∀ᵐ z ∂(J.measure : Measure Plane),
      0 < sweptNiche target (Real.pi / 2) z.2) :
    J.sourceBranchAngular (firstTangentSource target) 0 +
      J.sourceBranchAngular (firstCornerSource target) 0 =
        (volume.restrict (Ioo (0 : ℝ) (Real.pi / 2))).withDensity
          (fun t => ENNReal.ofReal (ρ t)) := by
  rw [J.first_branchAngular_sum hTarget.isCap hpositive,
    J.angularMeasure_eq_density hTarget hheight haffine hTargetBox hleft hright heq,
    restrict_withDensity measurableSet_Ioo,
    Measure.restrict_restrict_of_subset (Ioo_subset_Ioo le_rfl
      (show Real.pi / 2 ≤ Real.pi by linarith only [Real.pi_pos]))]

theorem second_branchAngular_sum_eq_density
    (hpositive : ∀ᵐ z ∂(J.measure : Measure Plane),
      0 < sweptNiche target (Real.pi / 2) z.2) :
    J.sourceBranchAngular (secondTangentSource target) (Real.pi / 2) +
      J.sourceBranchAngular (secondCornerSource target) (Real.pi / 2) =
        (volume.restrict (Ioo (0 : ℝ) (Real.pi / 2))).withDensity
          (fun t => ENNReal.ofReal (ρ (t + Real.pi / 2))) := by
  rw [J.second_branchAngular_sum hTarget.isCap hpositive,
    J.angularMeasure_eq_density hTarget hheight haffine hTargetBox hleft hright heq,
    restrict_withDensity measurableSet_Ioo,
    Measure.restrict_restrict_of_subset (Ioo_subset_Ioo
      (show (0 : ℝ) ≤ Real.pi / 2 by positivity) le_rfl), map_second_quarter_density hρ]

theorem ae_first_source_density_sum
    (hpositive : ∀ᵐ z ∂(J.measure : Measure Plane),
      0 < sweptNiche target (Real.pi / 2) z.2) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      J.sourceBranchDensity (firstTangentSource target) 0 t +
        J.sourceBranchDensity (firstCornerSource target) 0 t = ρ t := by
  have hsum := J.first_branchAngular_sum_eq_density hTarget hheight haffine hTargetBox
    hleft hright heq hpositive
  have hd := ae_realRnDensity_eq_on_of_withDensity_restrict measurableSet_Ioo hρ hρ0 hsum
  have ha := ae_realRnDensity_add (J.sourceBranchAngular (firstTangentSource target) 0)
    (J.sourceBranchAngular (firstCornerSource target) 0) volume
  filter_upwards [hd, ae_restrict_of_ae ha] with t ht hs
  exact hs.symm.trans ht

theorem ae_second_source_density_sum
    (hpositive : ∀ᵐ z ∂(J.measure : Measure Plane),
      0 < sweptNiche target (Real.pi / 2) z.2) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      J.sourceBranchDensity (secondTangentSource target) (Real.pi / 2) t +
        J.sourceBranchDensity (secondCornerSource target) (Real.pi / 2) t =
          ρ (t + Real.pi / 2) := by
  have hsum := J.second_branchAngular_sum_eq_density hTarget hheight haffine hTargetBox
    hleft hright hρ heq hpositive
  have hd := ae_realRnDensity_eq_on_of_withDensity_restrict measurableSet_Ioo
    (hρ.comp (measurable_id.add_const _)) (fun t => hρ0 (t + Real.pi / 2)) hsum
  have ha := ae_realRnDensity_add
    (J.sourceBranchAngular (secondTangentSource target) (Real.pi / 2))
    (J.sourceBranchAngular (secondCornerSource target) (Real.pi / 2)) volume
  filter_upwards [hd, ae_restrict_of_ae ha] with t ht hs
  exact hs.symm.trans ht

theorem ae_sourceBranchDensity_eq_zero_on
    {S : Set Plane} {d : ℝ} {E : Set ℝ} (hE : MeasurableSet E)
    (hzero : ∀ᵐ z ∂J.sourceBranchMeasure S, z.1 - d ∉ E) :
    ∀ᵐ t ∂volume, t ∈ E → J.sourceBranchDensity S d t = 0 := by
  have hz : J.sourceBranchAngular S d E = 0 := by
    rw [sourceBranchAngular, Measure.map_apply (measurable_fst.sub_const d) hE]
    exact measure_eq_zero_iff_ae_notMem.mpr hzero
  rw [J.sourceBranchAngular_eq_density hTarget hheight haffine hTargetBox hleft hright heq,
    withDensity_apply _ hE,
    lintegral_eq_zero_iff (J.measurable_sourceBranchDensity S d).ennreal_ofReal] at hz
  apply (ae_restrict_iff' hE).mp
  filter_upwards [hz] with t ht
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp ht) (J.sourceBranchDensity_nonneg S d t)

end ActualDensity
end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
