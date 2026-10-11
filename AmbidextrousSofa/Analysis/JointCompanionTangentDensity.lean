module

public import AmbidextrousSofa.Analysis.JointBranchProjection
public import AmbidextrousSofa.Analysis.JointSourceAffine
public import AmbidextrousSofa.Analysis.TangencyMeasurable

@[expose] public section

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
  (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
  {m c K : ℝ} {ρ : ℝ → ℝ}
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
    capRoof target x = m * x + c)
  (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
  (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature target).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))
  {C h : ℝ}
  (hl : horizontalLeft target = -2 * C) (hr : horizontalRight target = 2 * C)
  (hC : 1 / 2 < C) (hm : 0 < m)
  (hlow : capRoof target (-C) = 1 - h) (hhigh : capRoof target C = 1) (hh : 0 < h)
  (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1)

local notation "aD" => J.sourceBranchDensity (secondTangentSource target) (Real.pi / 2)
local notation "F" => fullTiltedSupportQuarterPair hTarget hm.le haffine hρ hρ0 hρK heq
set_option quotPrecheck false in
local notation "D" => secondTangentPoint (F).g (F).gD
local notation "v" => fun t => leftCompanionWingDensity m ρ (t + Real.pi / 2)

include hheight hTargetBox hleft hright hl hr hC hlow hhigh hh hunit in
theorem ae_companion_tangent_density_controls :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      aD t ≤ max (1 - v t) 0 ∧ (1 < v t → aD t = 0) ∧
        ((D t).2 < 0 → aD t = 0) := by
  have hcontact := J.ae_second_tangent_source_contact hTarget hheight haffine hTargetBox
    hleft hright hρ hρ0 hρK heq
  have hzero {E : Set ℝ} (hE : MeasurableSet E)
      (hz : ∀ᵐ z ∂J.sourceBranchMeasure (secondTangentSource target), z.1 - Real.pi / 2 ∉ E) :
      ∀ᵐ t ∂volume, t ∈ E → aD t = 0 :=
    J.ae_sourceBranchDensity_eq_zero_on hTarget hheight haffine hTargetBox hleft hright heq hE hz
  -- Strict contact excludes original companion curvature above one.
  have hexcess := hzero (measurableSet_lt measurable_const
    (hρ.comp (measurable_id.add_const (Real.pi / 2)))) (by
      filter_upwards [J.ae_second_tangent_source_density_le_one hTarget hheight haffine
        hTargetBox hleft hright hρ hρ0 hρK heq] with z hz
      simpa using hz)
  -- The companion tangent stays on the nonnegative niche.
  have hnegative := hzero (measurableSet_lt hTarget.isCap.measurable_secondTangency_snd
    measurable_const) (by
      filter_upwards [hcontact] with z hz
      simpa [← hz.2] using sweptNiche_nonneg target (Real.pi / 2) z.2)
  -- Every source angle lies beyond the affine normal.
  have hbefore := hzero measurableSet_Iic (by
    filter_upwards [ae_restrict_mem (measurableSet_secondTangentSource hTarget.isCap.isCompact),
      ae_restrict_of_ae (J.ae_sourceQuarterAngle_gt_affine hTarget hl hr hC hm hheight
        haffine hlow hhigh hh hρ hρ0 hρK heq hunit)] with z hz hp
    rw [sourceQuarterAngle, ite_eq_right (not_lt_of_ge hz.1.1.le)] at hp
    exact not_le_of_gt hp)
  have hD : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      HasDerivAt (fun s => (secondTangency target s).1)
        ((1 - ρ (t + Real.pi / 2)) * Real.cos t) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae (ae_regularCornerDomain_of_mem_quarter m),
      ae_restrict_of_ae ((ae_restrict_iff' (isOpen_regularCornerDomain m).measurableSet).mp
        (hTarget.isCap.ae_hasDerivAt_tangency_coordinates_on_regularCornerDomain
          hρ hρ0 hρK heq))] with t ht hr hd using (hd (hr ht)).2.2.1
  have hbound := J.ae_sourceBranchDensity_mul_sin_le_abs_deriv_on hTarget hheight haffine
    hTargetBox hleft hright heq (measurableSet_secondTangentSource hTarget.isCap.isCompact)
    (Real.pi / 2) hTarget.isCap.measurable_secondTangency_fst
    (by filter_upwards [hcontact] with z hz using congrArg Prod.fst hz.2) measurableSet_Ioo hD
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hbound, ae_restrict_of_ae hexcess,
    ae_restrict_of_ae hnegative, ae_restrict_of_ae hbefore,
    J.ae_original_companion_density_eq_cut hTarget hl hr hC hm hheight haffine hlow hhigh hh
      hρ hρ0 hρK heq hunit hTargetBox hleft hright] with t ht hb hex hneg hpre hcut
  have hle : aD t ≤ max (1 - ρ (t + Real.pi / 2)) 0 := by
    by_cases hle : ρ (t + Real.pi / 2) ≤ 1
    · have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
        ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
      rw [Real.sin_add_pi_div_two,
        abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hle) hc.le)] at hb
      exact (le_of_mul_le_mul_right hb hc).trans (le_max_left _ _)
    · exact (hex (lt_of_not_ge hle)).trans_le (le_max_right _ _)
  rw [hcut] at hle
  refine ⟨hle, fun hv => le_antisymm (hle.trans_eq (max_eq_right (by linarith only [hv])))
    (J.sourceBranchDensity_nonneg _ _ _), fun hy => ?_⟩
  by_cases hpre' : t ≤ Real.arctan m
  · exact hpre hpre'
  · exact hneg (by simpa only [(fullTiltedSupportQuarterPair_other_points_after_affine
      hTarget hm.le haffine hρ hρ0 hρK heq ⟨ht.1.le, ht.2⟩ (lt_of_not_ge hpre').le).1] using hy)

end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
