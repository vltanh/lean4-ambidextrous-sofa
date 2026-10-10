import AmbidextrousSofa.Analysis.FirstTangentExclusivity
import AmbidextrousSofa.Analysis.JointSourceNicheCalculus

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

variable {U : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit U a b)
  (hU : IsFullCapMaximizer U) {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ}
  (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

local notation "F" => fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
local notation "B" => firstTangentPoint F.f F.fD
local notation "p" => supportP F.fD F.g
local notation "q" => supportQ F.gD F.f

theorem ae_exclusive_first_source_on_positive_tangent {C α η : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1) (hmpos : 0 < m)
    (hleft : a < horizontalLeft U) (hright : horizontalRight U < b)
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1)
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) :
    ∀ᵐ z ∂(J.measure : Measure Plane), ∀ t ∈ Ioo (0 : ℝ) (Real.pi / 2),
      p t < 0 → 0 < (B t).2 → (B t).1 = z.2 →
        z ∈ firstTangentSource U ∧ z.1 = t := by
  have hC := (hU.centered_positive_tilt_parameters hl hr hheight hmpos haffine).1
  filter_upwards [J.ae_angle_mem_upper, J.ae_angle_ne (Real.pi / 2),
    J.ae_angle_ne α, J.ae_angle_ne η,
    J.ae_angle_ne (α + Real.pi / 2), J.ae_angle_ne (η + Real.pi / 2),
    J.ae_first_wall_contact hU.isCap, J.ae_second_wall_contact hU.isCap,
    J.ae_hasDerivAt_niche_on_source hU hl hr hC hleft hright]
      with z hz htop hα hη hα' hη' hfirst hsecond hderiv
  intro t ht hp hy hx
  have hD : HasDerivAt (sweptNiche U (Real.pi / 2)) (J.nicheDerivative z.2) (B t).1 := by
    simpa only [hx] using hderiv
  rcases lt_or_gt_of_ne htop with hbefore | hafter
  · have hquarter : z.1 ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨hz.1, hbefore⟩
    have hmax : fullWallClip hU.isCap.toCompactCap (B t).1 z.1 =
        sweptNiche U (Real.pi / 2) (B t).1 := by
      simpa only [hx] using (hfirst hquarter).2
    obtain ⟨hangle, hstrict⟩ := fullTiltedSupportQuarterPair_strict_first_contact_unique
      hU hm haffine hρ hρ0 hρK heq hl hr hheight hmpos hunit hphase
      ht hp hy hD hquarter hα hη hmax
    refine ⟨⟨hquarter, ?_⟩, hangle⟩
    simpa only [hx] using hstrict
  · have hupper : z.1 ∈ Ioo (Real.pi / 2) Real.pi := ⟨hafter, hz.2⟩
    have hquarter : z.1 - Real.pi / 2 ∈ Ioo (0 : ℝ) (Real.pi / 2) := by
      constructor <;> linarith only [hupper.1, hupper.2]
    have hneα : z.1 - Real.pi / 2 ≠ α := by
      intro he
      exact hα' (by linarith only [he])
    have hneη : z.1 - Real.pi / 2 ≠ η := by
      intro he
      exact hη' (by linarith only [he])
    have hmax : fullWallClip hU.isCap.toCompactCap (B t).1 (z.1 - Real.pi / 2) =
        sweptNiche U (Real.pi / 2) (B t).1 := by
      simpa only [hx] using (hsecond hupper).2
    have hstrict := (fullTiltedSupportQuarterPair_strict_first_contact_unique
      hU hm haffine hρ hρ0 hρK heq hl hr hheight hmpos hunit hphase
      ht hp hy hD hquarter hneα hneη hmax).2
    have hniche := fullTiltedSupportQuarterPair_niche_first_tangency
      hU hm haffine hρ hρ0 hρK heq hunit ht hp.le hy.le
    have hpositive : 0 < sweptNiche U (Real.pi / 2) (B t).1 := by
      rw [hniche]
      exact hy
    have hcorner := positive_fullWallClip_eq_cornerWall hpositive hmax
    have hfirst_eq : firstWall U (z.1 - Real.pi / 2) (B t).1 =
        sweptNiche U (Real.pi / 2) (B t).1 := by
      simpa only [cornerWall, min_eq_left hstrict.le] using hcorner
    have hsecond_eq : secondWall U (z.1 - Real.pi / 2) (B t).1 =
        sweptNiche U (Real.pi / 2) (B t).1 := by
      simpa only [hx] using (hsecond hupper).1
    exact False.elim (hstrict.ne (hfirst_eq.trans hsecond_eq.symm))

theorem ae_exclusive_first_source_on_image {C α η : ℝ} {S : Set ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1) (hmpos : 0 < m)
    (hleft : a < horizontalLeft U) (hright : horizontalRight U < b)
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1)
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η)
    (hS : ∀ t ∈ S, t ∈ Ioo (0 : ℝ) (Real.pi / 2) ∧ p t < 0 ∧ 0 < (B t).2) :
    ∀ᵐ z ∂(J.measure : Measure Plane), z.2 ∈ (fun t => (B t).1) '' S →
      z ∈ firstTangentSource U ∧ z.1 ∈ S := by
  filter_upwards [J.ae_exclusive_first_source_on_positive_tangent hU hm haffine hρ hρ0 hρK heq
    hl hr hheight hmpos hleft hright hunit hphase] with z hz
  rintro ⟨t, ht, hx⟩
  have hgood := hS t ht
  have hexclusive := hz t hgood.1 hgood.2.1 hgood.2.2 hx
  exact ⟨hexclusive.1, by simpa only [hexclusive.2] using ht⟩

end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
