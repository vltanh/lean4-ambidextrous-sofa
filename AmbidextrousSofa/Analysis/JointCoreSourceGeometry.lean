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

variable {target : Set Plane} {a b C h m c K : ℝ} {ρ : ℝ → ℝ}
  (H : IsTiltedFirstUnitTarget target a b C h m c ρ K)

set_option quotPrecheck false
local notation "F" => fullTiltedSupportQuarterPair H.hU H.hm.le H.haffine H.hρ H.hρ0 H.hρK H.heq
local notation "Z" => innerCornerPoint (F).f (F).g
local notation "p" => supportP (F).fD (F).g
local notation "q" => supportQ (F).gD (F).f
local notation "X" => (fun t => (Z t).1)
local notation "XD" => (fun t => p t * Real.cos t - q t * Real.sin t)

namespace IsTiltedFirstUnitTarget

include H

private theorem continuous_f_g : Continuous (F).f ∧ Continuous (F).g :=
  ⟨H.hU.isCap.imported_isConvexBody.continuous_supp,
    H.hU.isCap_fullLeftCompanion.imported_isConvexBody.continuous_supp.comp
      (continuous_id.add_const (Real.pi / 2))⟩

theorem core_continuous : Continuous (fun t => (Z t).1) ∧ Continuous (fun t => (Z t).2) := by
  obtain ⟨hf, hg⟩ := H.continuous_f_g
  constructor <;> dsimp only [innerCornerPoint] <;> fun_prop

theorem momenta_continuous : Continuous p ∧ Continuous q := by
  obtain ⟨hf, hg⟩ := H.continuous_f_g
  have hfD : Continuous (F).fD := H.hU.isCap.continuous_closedSupportDerivative H.hρ H.hρ0 H.hρK 0
  have hgD : Continuous (F).gD := H.hU.isCap_fullLeftCompanion.continuous_closedSupportDerivative
    (measurable_leftCompanionWingDensity H.hρ m)
    (fun t => (leftCompanionWingDensity_bounds H.hρ0 H.hρK t).1)
    (fun t => (leftCompanionWingDensity_bounds H.hρ0 H.hρK t).2) (Real.pi / 2)
  exact ⟨(hfD.sub hg).add continuous_const, (hgD.add hf).sub continuous_const⟩

theorem joint_corner_cofactors
    {α η t x : ℝ} {g : ℝ → ℝ} (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hmt : Real.arctan m ≤ t) (htα : t ≠ α) (htη : t ≠ η)
    (hpoint : (x, sweptNiche target (Real.pi / 2) x) = attachedCorner target t)
    (hderiv : HasDerivAt (sweptNiche target (Real.pi / 2)) (g x) x) :
    t ∈ Ioo α η ∧ x = (Z t).1 ∧
      (g (Z t).1 * Real.sin t + Real.cos t) * (p t * Real.cos t - q t * Real.sin t) = p t ∧
      (g (Z t).1 * Real.cos t - Real.sin t) * (p t * Real.cos t - q t * Real.sin t) = q t := by
  have hmatch := (fullTiltedSupportQuarterPair_other_points_after_affine
    H.hU H.hm.le H.haffine H.hρ H.hρ0 H.hρK H.heq ⟨ht.1.le, ht.2⟩ hmt).2
  have hx : x = (Z t).1 := congrArg Prod.fst (hpoint.trans hmatch.symm)
  have hn : sweptNiche target (Real.pi / 2) x = (Z t).2 :=
    congrArg Prod.snd (hpoint.trans hmatch.symm)
  subst hx
  have hchain := fullTiltedSupportQuarterPair_niche_core_slope
    H.hU H.hm.le H.haffine H.hρ H.hρ0 H.hρK H.heq ht hderiv hn
  rw [hmatch] at hderiv hn
  exact ⟨fullTiltedSupportQuarterPair_contact_mem_core_phase_of_after_affine H.hU H.hm.le H.haffine
    H.hρ H.hρ0 H.hρK H.heq hphase ht hmt htα htη hderiv hn, rfl,
    corner_graph_first_residual_identity hchain, corner_graph_second_residual_identity hchain⟩

end IsTiltedFirstUnitTarget

namespace AngularGrid.SelectedJointSourceLimit

variable (J : SelectedJointSourceLimit target a b)
include H

/-- Both corner branches lie on the core graph over the core phase, with the cofactor identity
of the niche derivative of their own family. -/
theorem ae_corner_core_geometry {α η : ℝ}
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) :
    (∀ᵐ z ∂J.sourceBranchMeasure (firstCornerSource target),
      z.1 ∈ Ioo α η ∧ z.2 = X z.1 ∧
        (J.nicheDerivative (X z.1) * Real.sin z.1 + Real.cos z.1) * XD z.1 = p z.1) ∧
    ∀ᵐ z ∂J.sourceBranchMeasure (secondCornerSource target),
      z.1 - Real.pi / 2 ∈ Ioo α η ∧ z.2 = X (z.1 - Real.pi / 2) ∧
        (J.nicheDerivative (X (z.1 - Real.pi / 2)) * Real.cos (z.1 - Real.pi / 2) -
          Real.sin (z.1 - Real.pi / 2)) * XD (z.1 - Real.pi / 2) = q (z.1 - Real.pi / 2) := by
  have hafter := J.ae_sourceQuarterAngle_gt_affine H
  have hd := J.ae_hasDerivAt_niche_on_source H
  have hK := H.hU.isCap.isCompact
  constructor
  · filter_upwards [ae_restrict_mem (measurableSet_firstCornerSource hK),
      ae_restrict_of_ae (J.ae_first_wall_contact H.hU.isCap), ae_restrict_of_ae hafter,
      ae_restrict_of_ae hd, ae_restrict_of_ae (J.ae_angle_ne α),
      ae_restrict_of_ae (J.ae_angle_ne η)] with z hz hc hafter hd hnα hnη
    rw [sourceQuarterAngle, ite_eq_left hz.1.2] at hafter
    exact (H.joint_corner_cofactors hphase hz.1 hafter.le hnα hnη (wall_tie_eq_attachedCorner hz.1
      (hc hz.1).1 (hz.2.symm.trans (hc hz.1).1)) hd).imp_right (And.imp_right And.left)
  · filter_upwards [ae_restrict_mem (measurableSet_secondCornerSource hK),
      ae_restrict_of_ae (J.ae_second_wall_contact H.hU.isCap), ae_restrict_of_ae hafter,
      ae_restrict_of_ae hd, ae_restrict_of_ae (J.ae_angle_ne (α + Real.pi / 2)),
      ae_restrict_of_ae (J.ae_angle_ne (η + Real.pi / 2))] with z hz hc hafter hd hnα hnη
    have ht : z.1 - Real.pi / 2 ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
    rw [sourceQuarterAngle, ite_eq_right (not_lt.2 hz.1.1.le)] at hafter
    exact (H.joint_corner_cofactors hphase ht hafter.le (fun he => hnα (by linarith only [he]))
      (fun he => hnη (by linarith only [he]))
      (wall_tie_eq_attachedCorner ht (hz.2.trans (hc hz.1).1) (hc hz.1).1) hd).imp_right
      (And.imp_right And.right)

end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
