module

public import AmbidextrousSofa.Analysis.JointCoreVisibility
public import AmbidextrousSofa.Analysis.JointFirstTangentSaturation
public import AmbidextrousSofa.Analysis.JointCompanionTangentDensity
public import AmbidextrousSofa.Analysis.CommonSourceCoefficients

@[expose] public section

/-!
# Actual common occupation for the tilted first-unit cap

The four literal source restrictions determine two tangent occupation
coefficients and one common corner coefficient. Their actual density
sums, tangent bounds, signed corner balance, and shared horizontal
budget give both source equations. Positive first-tangent contact
saturates its own coefficient, and unique positive core contact
saturates the same corner coefficient in both equations.

All occupation functions below are explicit clipped ratios of the
Radon--Nikodym branch densities. The first tangent uses the value one
on its measurable charged set, including zero-speed contacts.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa
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
  (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
  (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)

local notation "F" => fullTiltedSupportQuarterPair hU hm.le haffine hρ hρ0 hρK heq
set_option quotPrecheck false in
local notation "p" => supportP (F).fD (F).g
set_option quotPrecheck false in
local notation "q" => supportQ (F).gD (F).f
local notation "v" => (fun t : ℝ => leftCompanionWingDensity m ρ (t + Real.pi / 2))
set_option quotPrecheck false in
local notation "B" => firstTangentPoint (F).f (F).fD
set_option quotPrecheck false in
local notation "D" => secondTangentPoint (F).g (F).gD
set_option quotPrecheck false in
local notation "Z" => innerCornerPoint (F).f (F).g
local notation "aB" => J.sourceBranchDensity (firstTangentSource target) 0
local notation "aZ" => J.sourceBranchDensity (firstCornerSource target) 0
local notation "aD" => J.sourceBranchDensity (secondTangentSource target) (Real.pi / 2)
local notation "aW" => J.sourceBranchDensity (secondCornerSource target) (Real.pi / 2)

theorem exists_common_source_occupation_of_phases {α η : ℝ}
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) :
    ∃ b δ χ : ℝ → ℝ, Measurable δ ∧
      (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
        0 ≤ b t ∧ 0 ≤ δ t ∧ δ t ≤ 1 ∧ 0 ≤ χ t ∧ χ t ≤ 1) ∧
      (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
        ρ t = (1 - ρ t) * b t + q t * χ t ∧
          v t = (1 - v t) * δ t - p t * χ t) ∧
      (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
        (p t < 0 → (B t).1 ∈ Ioo (-C) C → 0 < (B t).2 →
          sweptNiche target (Real.pi / 2) (B t).1 = (B t).2 → b t = 1) ∧
        (C ≤ (B t).1 → b t = 0)) ∧
      (∀ᵐ t ∂volume.restrict (regularCornerDomain m),
        p t < 0 → 0 < q t → (Z t).1 ∈ Ioo (-C) C → 0 < (Z t).2 →
        sweptNiche target (Real.pi / 2) (Z t).1 = (Z t).2 →
        (∀ s ∈ Icc (0 : ℝ) (Real.pi / 2),
          fullWallClip hU.isCap.toCompactCap (Z t).1 s =
            sweptNiche target (Real.pi / 2) (Z t).1 → s = t) → χ t = 1) ∧
      (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
        ((D t).2 < 0 → δ t = 0) ∧ (1 < v t → δ t = 0)) := by
  let charged : Set ℝ := firstTangentChargedSet target C p B
  let bfun : ℝ → ℝ := Analysis.firstSourceCoefficient charged aB ρ
  let δ : ℝ → ℝ := Analysis.companionSourceCoefficient aD v
  let χ : ℝ → ℝ := Analysis.cornerSourceCoefficient aZ q
  have hcharged : MeasurableSet charged :=
    fullTiltedSupportQuarterPair_measurableSet_firstTangentChargedSet
      hU hm.le haffine hρ hρ0 hρK heq C
  have hbmeas : Measurable bfun := Analysis.measurable_firstSourceCoefficient
    hcharged (J.measurable_sourceBranchDensity _ _) hρ
  have hδmeas : Measurable δ := Analysis.measurable_companionSourceCoefficient
    (J.measurable_sourceBranchDensity _ _)
    ((measurable_leftCompanionWingDensity hρ m).comp (measurable_id.add_const (Real.pi / 2)))
  have hχmeas : Measurable χ := Analysis.measurable_cornerSourceCoefficient
    (J.measurable_sourceBranchDensity _ _)
    (fullTiltedSupportQuarterPair_momenta_continuous hU hm.le haffine hρ hρ0 hρK heq).2.measurable
  have hpositive := J.ae_niche_pos_of_first_unit hU hl hr hC hm hheight haffine
    hlow hhigh hh hρ hρ0 hρK heq hunit
  have hfirstSum := J.ae_first_source_density_sum hU hheight haffine hTargetBox
    hleft hright hρ hρ0 heq hpositive
  have hsecondSum := J.ae_second_source_density_sum hU hheight haffine hTargetBox
    hleft hright hρ hρ0 heq hpositive
  have hcut := J.ae_original_companion_density_eq_cut hU hl hr hC hm hheight haffine
    hlow hhigh hh hρ hρ0 hρK heq hunit hTargetBox hleft hright
  have hBbound := J.ae_first_tangent_density_le_one_sub hU hheight haffine
    hTargetBox hleft hright hρ hρ0 hρK heq hunit
  have hDcontrols := J.ae_companion_tangent_density_controls hU hheight haffine
    hTargetBox hleft hright hρ hρ0 hρK heq hl hr hC hm hlow hhigh hh hunit
  have hBsaturated := J.ae_first_tangent_density_eq_one_sub_on_charged
    hU hl hr hC hm hheight haffine hlow hhigh hh hρ hρ0 hρK heq hunit
    hTargetBox hleft hright hphase
  have hcornerZero := J.ae_corner_density_zero_off_core hU hl hr hC hm hheight haffine
    hlow hhigh hh hρ hρ0 hρK heq hunit hTargetBox hleft hright hphase
  have hcornerBalance := J.ae_corner_density_balance hU hl hr hC hm hheight haffine
    hlow hhigh hh hρ hρ0 hρK heq hunit hTargetBox hleft hright hphase
  have hcornerProjection := (ae_restrict_iff' measurableSet_Ioo).mp
    (J.ae_corner_source_weighted_sum_le_core_speed hU hl hr hC hm hheight haffine
      hlow hhigh hh hρ hρ0 hρK heq hunit hTargetBox hleft hright hphase)
  refine ⟨bfun, δ, χ, hδmeas, ?_, ?_, ?_, ?_, ?_⟩
  · exact ae_of_all _ (fun t =>
      ⟨(Analysis.firstSourceCoefficient_bounds charged aB ρ t).1,
        (Analysis.companionSourceCoefficient_bounds aD v t).1,
        (Analysis.companionSourceCoefficient_bounds aD v t).2,
        (Analysis.cornerSourceCoefficient_bounds aZ q t).1,
        (Analysis.cornerSourceCoefficient_bounds aZ q t).2⟩)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo, hfirstSum, hsecondSum, hcut,
      hBbound, hDcontrols, hBsaturated, ae_restrict_of_ae hcornerZero,
      hcornerBalance, ae_restrict_of_ae hcornerProjection]
      with t ht hfirst hsecond hcutEq hB hD hchargedEq hzero hbalance hprojection
    apply Analysis.commonSourceCoefficients_balance ht
      (J.sourceBranchDensity_nonneg _ _ _) (J.sourceBranchDensity_nonneg _ _ _)
      (J.sourceBranchDensity_nonneg _ _ _)
      hfirst.symm (hcutEq.symm.trans hsecond.symm) hB hD.1 hchargedEq
    · intro hnot
      exact hzero (fun hc => hnot (hphase.core_signs t hc))
    · exact hbalance
    · intro hp hq
      exact hprojection
        (hphase.mem_core_of_first_neg_second_pos (Ioo_subset_Icc_self ht) hp hq)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae (J.ae_first_tangent_density_eq_zero_after_middle
        hU hheight haffine hTargetBox hleft hright hρ hρ0 hρK heq hl hr)] with t ht hzero
    constructor
    · intro hp hx hy hcontact
      exact Analysis.firstSourceCoefficient_eq_one_of_mem
        (show t ∈ charged from ⟨hp, hx, hy, hcontact⟩)
    · intro hx
      have hnot : t ∉ charged := by
        intro hc
        exact (not_lt_of_ge hx) hc.2.1.2
      have hmatch := fullTiltedSupportQuarterPair_first_tangency
        hU hm.le haffine hρ hρ0 hρK heq ⟨ht.1.le, ht.2⟩
      exact Analysis.firstSourceCoefficient_eq_zero_of_not_mem hnot
        (hzero (by simpa only [hmatch] using hx))
  · filter_upwards [J.ae_first_corner_density_eq_q_of_unique_contact
      hU hl hr hC hm hheight haffine hlow hhigh hh hρ hρ0 hρK heq hunit
      hTargetBox hleft hright hphase] with t hmass
    intro hp hq hx hy hcontact hunique
    exact Analysis.cornerSourceCoefficient_eq_one_of_mass_eq hq
      (hmass hp hq hx hy hcontact hunique)
  · filter_upwards [hDcontrols] with t ht
    exact ⟨fun hy => Analysis.companionSourceCoefficient_eq_zero_of_mass_zero (ht.2.2 hy),
      fun hv => Analysis.companionSourceCoefficient_eq_zero_of_one_le hv.le⟩

end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
