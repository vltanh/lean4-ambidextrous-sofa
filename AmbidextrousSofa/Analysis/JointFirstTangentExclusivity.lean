module

public import AmbidextrousSofa.Analysis.FirstTangentExclusivity
public import AmbidextrousSofa.Analysis.JointSourceNicheCalculus

@[expose] public section

/-!
# Exclusive first-family support over a positive first tangent

The selected joint source has a differentiable niche at almost every
source abscissa and no mass at the two core endpoint angles in either
family. The pointwise first-tangent exclusivity theorem therefore
identifies every source over a positive active first tangent, including
its original angular coordinate. This statement can be applied to an
entire open image interval without choosing an inverse of the tangent.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa
namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b C h m c K : ℝ} {ρ : ℝ → ℝ}
  (J : SelectedJointSourceLimit target a b) (H : IsTiltedFirstUnitTarget target a b C h m c ρ K)

set_option quotPrecheck false
local notation "F" => fullTiltedSupportQuarterPair H.hU H.hm.le H.haffine H.hρ H.hρ0 H.hρK H.heq
local notation "B" => firstTangentPoint (F).f (F).fD
local notation "p" => supportP (F).fD (F).g
local notation "q" => supportQ (F).gD (F).f

theorem ae_exclusive_first_source_on_image {α η : ℝ} {S : Set ℝ}
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η)
    (hS : ∀ t ∈ S, t ∈ Ioo (0 : ℝ) (Real.pi / 2) ∧ p t < 0 ∧ 0 < (B t).2) :
    ∀ᵐ z ∂(J.measure : Measure Plane), z.2 ∈ (fun t => (B t).1) '' S →
      z ∈ firstTangentSource target ∧ z.1 ∈ S := by
  filter_upwards [J.ae_angle_mem_upper, J.ae_angle_ne (Real.pi / 2), J.ae_angle_ne α,
    J.ae_angle_ne η, J.ae_angle_ne (α + Real.pi / 2), J.ae_angle_ne (η + Real.pi / 2),
    J.ae_first_wall_contact H.hU.isCap, J.ae_second_wall_contact H.hU.isCap,
    J.ae_hasDerivAt_niche_on_source H]
    with z hz htop hα hη hα' hη' hfirst hsecond hderiv
  rintro ⟨t, htS, hx⟩
  obtain ⟨ht, hp, hy⟩ := hS t htS
  dsimp only at hx
  rw [← hx] at hderiv hfirst hsecond
  have hunique {s : ℝ} := fullTiltedSupportQuarterPair_strict_first_contact_unique (s := s) H.hU
    H.hm.le H.haffine H.hρ H.hρ0 H.hρK H.heq H.hl H.hr H.hheight H.hm H.hunit hphase ht hp hy hderiv
  rcases lt_or_gt_of_ne htop with hbefore | hafter
  · obtain ⟨rfl, hstrict⟩ := hunique ⟨hz.1, hbefore⟩ hα hη (hfirst ⟨hz.1, hbefore⟩).2
    exact ⟨⟨⟨hz.1, hbefore⟩, by rwa [hx] at hstrict⟩, htS⟩
  · have hupper : z.1 ∈ Ioo (Real.pi / 2) Real.pi := ⟨hafter, hz.2⟩
    have hstrict := (hunique ⟨by linarith [hupper.1], by linarith [hupper.2]⟩
      (fun he => hα' (by linarith)) (fun he => hη' (by linarith)) (hsecond hupper).2).2
    have hpos : 0 < sweptNiche target (Real.pi / 2) (B t).1 := by
      rwa [fullTiltedSupportQuarterPair_niche_first_tangency H.hU H.hm.le H.haffine H.hρ H.hρ0
        H.hρK H.heq H.hunit ht hp.le hy.le]
    have hcorner : cornerWall target (z.1 - Real.pi / 2) (B t).1 =
        sweptNiche target (Real.pi / 2) (B t).1 :=
      positive_fullWallClip_eq_cornerWall (U := H.hU.isCap.toCompactCap) hpos (hsecond hupper).2
    rw [cornerWall, min_eq_left hstrict.le] at hcorner
    exact (hstrict.ne (hcorner.trans (hsecond hupper).1.symm)).elim

end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
