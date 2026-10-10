module

public import AmbidextrousSofa.Analysis.JointSourceNicheCalculus
public import AmbidextrousSofa.Analysis.JointBranchIntegrals
public import AmbidextrousSofa.Analysis.CoreContactPhase

@[expose] public section

/-!
# The actual graph and phase of both corner source restrictions

Both literal corner restrictions are concentrated on the same strictly
ordered core phase. Their common spatial coordinate is the closed
two-cap corner coordinate. At almost every source contact, the actual
niche derivative gives the two exact cofactor identities needed to
identify one corner occupation factor.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

section ActualPair

variable {U : Set Plane} (hU : IsFullCapMaximizer U)
  {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

local notation "F" => fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
set_option quotPrecheck false in
local notation "Z" => innerCornerPoint (F).f (F).g
set_option quotPrecheck false in
local notation "p" => supportP (F).fD (F).g
set_option quotPrecheck false in
local notation "q" => supportQ (F).gD (F).f

theorem fullTiltedSupportQuarterPair_core_continuous_global :
    Continuous (fun t => (Z t).1) ∧ Continuous (fun t => (Z t).2) := by
  have hf : Continuous (F).f := hU.isCap.imported_isConvexBody.continuous_supp
  have hg : Continuous (F).g :=
    hU.isCap_fullLeftCompanion.imported_isConvexBody.continuous_supp.comp
      (continuous_id.add_const (Real.pi / 2))
  constructor <;> dsimp only [innerCornerPoint] <;> fun_prop

theorem fullTiltedSupportQuarterPair_momenta_continuous : Continuous p ∧ Continuous q := by
  have hf : Continuous (F).f := hU.isCap.imported_isConvexBody.continuous_supp
  have hg : Continuous (F).g :=
    hU.isCap_fullLeftCompanion.imported_isConvexBody.continuous_supp.comp
      (continuous_id.add_const (Real.pi / 2))
  have hfD : Continuous (F).fD := hU.isCap.continuous_closedSupportDerivative hρ hρ0 hρK 0
  have hgD : Continuous (F).gD := hU.isCap_fullLeftCompanion.continuous_closedSupportDerivative
    (measurable_leftCompanionWingDensity hρ m)
    (fun t => (leftCompanionWingDensity_bounds hρ0 hρK t).1)
    (fun t => (leftCompanionWingDensity_bounds hρ0 hρK t).2) (Real.pi / 2)
  exact ⟨(hfD.sub hg).add continuous_const, (hgD.add hf).sub continuous_const⟩

theorem fullTiltedSupportQuarterPair_joint_corner_cofactors
    {t x : ℝ} {g : ℝ → ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hmt : Real.arctan m ≤ t)
    (hpoint : (x, sweptNiche U (Real.pi / 2) x) = attachedCorner U t)
    (hderiv : HasDerivAt (sweptNiche U (Real.pi / 2)) (g x) x) :
    x = (Z t).1 ∧
      (g (Z t).1 * Real.sin t + Real.cos t) *
        (p t * Real.cos t - q t * Real.sin t) = p t ∧
      (g (Z t).1 * Real.cos t - Real.sin t) *
        (p t * Real.cos t - q t * Real.sin t) = q t := by
  have hmatch := (fullTiltedSupportQuarterPair_other_points_after_affine
    hU hm haffine hρ hρ0 hρK heq ⟨ht.1.le, ht.2⟩ hmt).2
  have hclosed := hpoint.trans hmatch.symm
  have hx : x = (Z t).1 := congrArg Prod.fst hclosed
  have hn : sweptNiche U (Real.pi / 2) x = (Z t).2 := congrArg Prod.snd hclosed
  rw [hx] at hn hderiv
  have hchain := fullTiltedSupportQuarterPair_niche_core_slope
    hU hm haffine hρ hρ0 hρK heq ht hderiv hn
  exact ⟨hx, corner_graph_first_residual_identity hchain,
    corner_graph_second_residual_identity hchain⟩

end ActualPair

namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)
  (hU : IsFullCapMaximizer target) {C h m c : ℝ}
  (hl : horizontalLeft target = -2 * C) (hr : horizontalRight target = 2 * C)
  (hC : 1 / 2 < C) (hm : 0 < m) (hheight : capHeight target = 1)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
    capRoof target x = m * x + c)
  (hlow : capRoof target (-C) = 1 - h) (hhigh : capRoof target C = 1) (hh : 0 < h)
  {ρ : ℝ → ℝ} {K : ℝ} (hρ : Measurable ρ)
  (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature target).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))
  (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1)
  (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)

local notation "F" => fullTiltedSupportQuarterPair hU hm.le haffine hρ hρ0 hρK heq
set_option quotPrecheck false in
local notation "Z" => innerCornerPoint (F).f (F).g
set_option quotPrecheck false in
local notation "p" => supportP (F).fD (F).g
set_option quotPrecheck false in
local notation "q" => supportQ (F).gD (F).f
set_option quotPrecheck false in
local notation "X" => (fun t => (Z t).1)
local notation "XD" => (fun t => p t * Real.cos t - q t * Real.sin t)

include hl hr hC hheight hlow hhigh hh hunit hleft hright in
theorem ae_first_corner_core_geometry {α η : ℝ}
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) :
    ∀ᵐ z ∂J.sourceBranchMeasure (firstCornerSource target),
      z.1 ∈ Ioo α η ∧ z.2 = X z.1 ∧
        (J.nicheDerivative (X z.1) * Real.sin z.1 + Real.cos z.1) * XD z.1 = p z.1 := by
  filter_upwards [J.ae_first_corner_source_contact hU.isCap,
    ae_restrict_of_ae (J.ae_sourceQuarterAngle_gt_affine hU hl hr hC hm hheight haffine
      hlow hhigh hh hρ hρ0 hρK heq hunit),
    ae_restrict_of_ae (J.ae_hasDerivAt_niche_on_source hU hl hr hC hleft hright),
    ae_restrict_of_ae (J.ae_angle_ne α), ae_restrict_of_ae (J.ae_angle_ne η)]
    with z hc hafter hd hnα hnη
  have hmt : Real.arctan m < z.1 := by
    simpa only [sourceQuarterAngle, if_pos hc.1.2] using hafter
  have hcalc := fullTiltedSupportQuarterPair_joint_corner_cofactors
    hU hm.le haffine hρ hρ0 hρK heq hc.1 hmt.le hc.2 hd
  have hx : z.2 = (attachedCorner target z.1).1 := congrArg Prod.fst hc.2
  have hn : sweptNiche target (Real.pi / 2) z.2 =
      (attachedCorner target z.1).2 := congrArg Prod.snd hc.2
  rw [hx] at hd hn
  have hcore := fullTiltedSupportQuarterPair_contact_mem_core_phase_of_after_affine
    hU hm.le haffine hρ hρ0 hρK heq hphase hc.1 hmt.le hnα hnη hd hn
  exact ⟨hcore, hcalc.1, hcalc.2.1⟩

include hl hr hC hheight hlow hhigh hh hunit hleft hright in
theorem ae_second_corner_core_geometry {α η : ℝ}
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) :
    ∀ᵐ z ∂J.sourceBranchMeasure (secondCornerSource target),
      z.1 - Real.pi / 2 ∈ Ioo α η ∧ z.2 = X (z.1 - Real.pi / 2) ∧
        (J.nicheDerivative (X (z.1 - Real.pi / 2)) * Real.cos (z.1 - Real.pi / 2) -
          Real.sin (z.1 - Real.pi / 2)) * XD (z.1 - Real.pi / 2) =
            q (z.1 - Real.pi / 2) := by
  filter_upwards [J.ae_second_corner_source_contact hU.isCap,
    ae_restrict_of_ae (J.ae_sourceQuarterAngle_gt_affine hU hl hr hC hm hheight haffine
      hlow hhigh hh hρ hρ0 hρK heq hunit),
    ae_restrict_of_ae (J.ae_hasDerivAt_niche_on_source hU hl hr hC hleft hright),
    ae_restrict_of_ae (J.ae_angle_ne (α + Real.pi / 2)),
    ae_restrict_of_ae (J.ae_angle_ne (η + Real.pi / 2))] with z hc hafter hd hnα hnη
  have hL : Real.pi / 2 < z.1 := by linarith only [hc.1.1]
  have hmt : Real.arctan m < z.1 - Real.pi / 2 := by
    simpa only [sourceQuarterAngle, if_neg (not_lt_of_ge hL.le)] using hafter
  have hcalc := fullTiltedSupportQuarterPair_joint_corner_cofactors
    hU hm.le haffine hρ hρ0 hρK heq hc.1 hmt.le hc.2 hd
  have hx : z.2 = (attachedCorner target (z.1 - Real.pi / 2)).1 := congrArg Prod.fst hc.2
  have hn : sweptNiche target (Real.pi / 2) z.2 =
      (attachedCorner target (z.1 - Real.pi / 2)).2 := congrArg Prod.snd hc.2
  rw [hx] at hd hn
  have hcore := fullTiltedSupportQuarterPair_contact_mem_core_phase_of_after_affine
    hU hm.le haffine hρ hρ0 hρK heq hphase hc.1 hmt.le
    (fun he => hnα (by linarith only [he])) (fun he => hnη (by linarith only [he])) hd hn
  exact ⟨hcore, hcalc.1, hcalc.2.2⟩

end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
