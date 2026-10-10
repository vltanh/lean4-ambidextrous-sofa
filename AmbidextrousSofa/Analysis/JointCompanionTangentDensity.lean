import AmbidextrousSofa.Analysis.JointBranchProjection
import AmbidextrousSofa.Analysis.JointSourceAffine
import AmbidextrousSofa.Analysis.TangencyMeasurable

/-!
# The actual companion tangent occupation density

The companion tangent branch is one literal restriction of the common
source measure. Its horizontal projection bounds its angular density by
the absolute companion tangent speed. Actual strict-contact calculus
removes the region where the original companion curvature exceeds one,
so the resulting bound is the positive part of one minus curvature.
The proved affine-source exclusion then transfers this bound to the
literal cut companion and removes tangent occupation below its floor.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa
namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

section ActualDensity

variable (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
  {m c K : ℝ} {ρ : ℝ → ℝ}
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
    capRoof target x = m * x + c)
  (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
  (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature target).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

local notation "aD" => J.sourceBranchDensity (secondTangentSource target) (Real.pi / 2)

theorem ae_second_tangent_source_graph :
    ∀ᵐ z ∂J.sourceBranchMeasure (secondTangentSource target),
      z.2 = (secondTangency target (z.1 - Real.pi / 2)).1 := by
  filter_upwards [J.ae_second_tangent_source_contact hTarget hheight haffine
    hTargetBox hleft hright hρ hρ0 hρK heq] with z hz
  exact congrArg Prod.fst hz.2

theorem ae_second_tangent_density_eq_zero_of_original_excess :
    ∀ᵐ t ∂volume, 1 < ρ (t + Real.pi / 2) → aD t = 0 := by
  let E : Set ℝ := {t | 1 < ρ (t + Real.pi / 2)}
  have hE : MeasurableSet E := measurableSet_lt measurable_const
    (hρ.comp (measurable_id.add_const (Real.pi / 2)))
  have hz : ∀ᵐ z ∂J.sourceBranchMeasure (secondTangentSource target),
      z.1 - Real.pi / 2 ∉ E := by
    filter_upwards [J.ae_second_tangent_source_density_le_one hTarget hheight haffine
      hTargetBox hleft hright hρ hρ0 hρK heq] with z hz
    simpa only [E, mem_setOf_eq, sub_add_cancel] using not_lt_of_ge hz
  exact J.ae_sourceBranchDensity_eq_zero_on hTarget hheight haffine hTargetBox
    hleft hright heq hE hz

theorem ae_second_tangent_density_eq_zero_of_original_negative :
    ∀ᵐ t ∂volume, (secondTangency target t).2 < 0 → aD t = 0 := by
  let E : Set ℝ := {t | (secondTangency target t).2 < 0}
  have hE : MeasurableSet E := measurableSet_lt
    hTarget.isCap.measurable_secondTangency_snd measurable_const
  have hz : ∀ᵐ z ∂J.sourceBranchMeasure (secondTangentSource target),
      z.1 - Real.pi / 2 ∉ E := by
    filter_upwards [J.ae_second_tangent_source_contact hTarget hheight haffine
      hTargetBox hleft hright hρ hρ0 hρK heq] with z hz
    have hy : sweptNiche target (Real.pi / 2) z.2 =
        (secondTangency target (z.1 - Real.pi / 2)).2 := congrArg Prod.snd hz.2
    change ¬ (secondTangency target (z.1 - Real.pi / 2)).2 < 0
    rw [← hy]
    exact not_lt_of_ge (sweptNiche_nonneg _ _ _)
  exact J.ae_sourceBranchDensity_eq_zero_on hTarget hheight haffine hTargetBox
    hleft hright heq hE hz

theorem ae_second_tangent_density_le_max_one_sub_original :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      aD t ≤ max (1 - ρ (t + Real.pi / 2)) 0 := by
  have hDregular := (ae_restrict_iff'
    (isOpen_regularCornerDomain m).measurableSet).mp
      (hTarget.isCap.ae_hasDerivAt_tangency_coordinates_on_regularCornerDomain
        hρ hρ0 hρK heq)
  have hD : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      HasDerivAt (fun s => (secondTangency target s).1)
        ((1 - ρ (t + Real.pi / 2)) * Real.cos t) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae (ae_regularCornerDomain_of_mem_quarter m),
      ae_restrict_of_ae hDregular] with t ht hr hd
    exact (hd (hr ht)).2.2.1
  have hgraph := J.ae_second_tangent_source_graph hTarget hheight haffine hTargetBox
    hleft hright hρ hρ0 hρK heq
  have hbound := J.ae_sourceBranchDensity_mul_sin_le_abs_deriv_on hTarget hheight haffine
    hTargetBox hleft hright heq (measurableSet_secondTangentSource hTarget.isCap.isCompact)
    (Real.pi / 2) hTarget.isCap.measurable_secondTangency_fst hgraph measurableSet_Ioo hD
  filter_upwards [hbound, ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae (J.ae_second_tangent_density_eq_zero_of_original_excess
      hTarget hheight haffine hTargetBox hleft hright hρ hρ0 hρK heq)] with t hb ht hz
  by_cases hle : ρ (t + Real.pi / 2) ≤ 1
  · have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
      ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
    rw [Real.sin_add_pi_div_two,
      abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hle) hc.le)] at hb
    exact ((mul_le_mul_right hc).mp hb).trans (le_max_left _ _)
  · rw [hz (lt_of_not_ge hle)]
    exact le_max_right _ _

section PositiveTilt

variable {C h : ℝ}
  (hl : horizontalLeft target = -2 * C) (hr : horizontalRight target = 2 * C)
  (hC : 1 / 2 < C) (hm : 0 < m)
  (hlow : capRoof target (-C) = 1 - h) (hhigh : capRoof target C = 1) (hh : 0 < h)
  (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1)

local notation "F" => fullTiltedSupportQuarterPair hTarget hm.le haffine hρ hρ0 hρK heq
local notation "D" => secondTangentPoint F.g F.gD
local notation "v" => fun t => leftCompanionWingDensity m ρ (t + Real.pi / 2)

theorem ae_companion_tangent_density_le_max_one_sub :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), aD t ≤ max (1 - v t) 0 := by
  have hequal := J.ae_original_companion_density_eq_cut hTarget hl hr hC hm hheight
    haffine hlow hhigh hh hρ hρ0 hρK heq hunit hTargetBox hleft hright
  filter_upwards [hequal, J.ae_second_tangent_density_le_max_one_sub_original
    hTarget hheight haffine hTargetBox hleft hright hρ hρ0 hρK heq] with t ht hb
  simpa only [ht] using hb

theorem ae_companion_tangent_density_eq_zero_through_affine :
    ∀ᵐ t ∂volume, t ≤ Real.arctan m → aD t = 0 := by
  have hz : ∀ᵐ z ∂J.sourceBranchMeasure (secondTangentSource target),
      z.1 - Real.pi / 2 ∉ Iic (Real.arctan m) := by
    filter_upwards [ae_restrict_mem (measurableSet_secondTangentSource hTarget.isCap.isCompact),
      ae_restrict_of_ae (J.ae_sourceQuarterAngle_gt_affine hTarget hl hr hC hm hheight
        haffine hlow hhigh hh hρ hρ0 hρK heq hunit)] with z hz hp
    rw [sourceQuarterAngle, if_neg (not_lt_of_ge hz.1.1.le)] at hp
    exact not_le_of_gt hp
  exact J.ae_sourceBranchDensity_eq_zero_on hTarget hheight haffine hTargetBox
    hleft hright heq measurableSet_Iic hz

theorem ae_companion_tangent_density_eq_zero_of_excess :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), 1 < v t → aD t = 0 := by
  filter_upwards [J.ae_companion_tangent_density_le_max_one_sub hTarget hheight haffine
    hTargetBox hleft hright hρ hρ0 hρK heq hl hr hC hm hlow hhigh hh hunit] with t ht
  intro hv
  have hmax : max (1 - v t) 0 = 0 := max_eq_right (by linarith only [hv])
  rw [hmax] at ht
  exact le_antisymm ht (J.sourceBranchDensity_nonneg _ _ _)

theorem ae_companion_tangent_density_eq_zero_of_negative :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), (D t).2 < 0 → aD t = 0 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae (J.ae_second_tangent_density_eq_zero_of_original_negative
      hTarget hheight haffine hTargetBox hleft hright hρ hρ0 hρK heq),
    ae_restrict_of_ae (J.ae_companion_tangent_density_eq_zero_through_affine
      hTarget hheight haffine hTargetBox hleft hright hρ hρ0 hρK heq hl hr hC hm
        hlow hhigh hh hunit)] with t ht hnegative hbefore
  intro hy
  by_cases hpre : t ≤ Real.arctan m
  · exact hbefore hpre
  · have hmatch := (fullTiltedSupportQuarterPair_other_points_after_affine
      hTarget hm.le haffine hρ hρ0 hρK heq ⟨ht.1.le, ht.2⟩ (lt_of_not_ge hpre).le).1
    exact hnegative (by simpa only [hmatch] using hy)

theorem ae_companion_tangent_density_controls :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      aD t ≤ max (1 - v t) 0 ∧ (1 < v t → aD t = 0) ∧
        ((D t).2 < 0 → aD t = 0) := by
  filter_upwards [J.ae_companion_tangent_density_le_max_one_sub hTarget hheight haffine
    hTargetBox hleft hright hρ hρ0 hρK heq hl hr hC hm hlow hhigh hh hunit,
    J.ae_companion_tangent_density_eq_zero_of_excess hTarget hheight haffine hTargetBox
      hleft hright hρ hρ0 hρK heq hl hr hC hm hlow hhigh hh hunit,
    J.ae_companion_tangent_density_eq_zero_of_negative hTarget hheight haffine hTargetBox
      hleft hright hρ hρ0 hρK heq hl hr hC hm hlow hhigh hh hunit] with t hb he hn
  exact ⟨hb, he, hn⟩

end PositiveTilt
end ActualDensity
end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
