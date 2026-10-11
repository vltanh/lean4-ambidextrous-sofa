module

public import AmbidextrousSofa.Analysis.JointFirstTangentDensity
public import AmbidextrousSofa.Analysis.JointFirstTangentExclusivity
public import AmbidextrousSofa.Analysis.JointCoreProjectionEquality
public import AmbidextrousSofa.Measure.MonotoneGraphSaturation

@[expose] public section

/-!
# Saturation of the actual charged first tangent

Above a positive first tangent with negative first momentum, every
source has that same first-family angle. Its sine-weighted angular
mass on any measurable charged parameter set therefore equals the
horizontal source mass on the tangent image. The latter is ordinary
length inside the positive middle niche. The monotone area formula
then identifies the branch density with the first tangent speed,
including parameter sets on which that speed is zero.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

def firstTangentChargedSet (U : Set Plane) (C : ℝ) (p : ℝ → ℝ)
    (B : ℝ → Plane) : Set ℝ :=
  {t | p t < 0 ∧ (B t).1 ∈ Ioo (-C) C ∧ 0 < (B t).2 ∧
    sweptNiche U (Real.pi / 2) (B t).1 = (B t).2}

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
local notation "B" => firstTangentPoint (F).f (F).fD
set_option quotPrecheck false in
local notation "p" => supportP (F).fD (F).g

theorem fullTiltedSupportQuarterPair_measurableSet_firstTangentChargedSet (C : ℝ) :
    MeasurableSet (firstTangentChargedSet U C p B) := by
  have hf : Continuous (F).f := hU.isCap.imported_isConvexBody.continuous_supp
  have hfD : Continuous (F).fD := hU.isCap.continuous_closedSupportDerivative hρ hρ0 hρK 0
  have hB : Continuous B := by unfold firstTangentPoint Reference.supportPoint; fun_prop
  exact (measurableSet_lt (fullTiltedSupportQuarterPair_momenta_continuous
    hU hm haffine hρ hρ0 hρK heq).1.measurable measurable_const).inter
    ((measurableSet_Ioo.preimage hB.fst.measurable).inter
      ((measurableSet_lt measurable_const hB.snd.measurable).inter (measurableSet_eq_fun
        (hU.isCap.continuous_sweptNiche_pi_div_two.comp hB.fst).measurable hB.snd.measurable)))

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
  (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
  (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)

local notation "F" => fullTiltedSupportQuarterPair hU hm.le haffine hρ hρ0 hρK heq
set_option quotPrecheck false in
local notation "B" => firstTangentPoint (F).f (F).fD
set_option quotPrecheck false in
local notation "p" => supportP (F).fD (F).g
set_option quotPrecheck false in
local notation "q" => supportQ (F).gD (F).f
set_option quotPrecheck false in
local notation "X" => (fun t => (B t).1)
local notation "aB" => J.sourceBranchDensity (firstTangentSource target) 0
local notation "charged" => firstTangentChargedSet target C p B

include hl hr hC hheight hlow hhigh hh hunit hTargetBox hleft hright in
theorem ae_first_tangent_density_eq_one_sub_on_charged {α η : ℝ}
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      t ∈ charged → aB t = 1 - ρ t := by
  have hc := fullTiltedSupportQuarterPair_measurableSet_firstTangentChargedSet
    hU hm.le haffine hρ hρ0 hρK heq C
  set S := charged ∩ Ioo (0 : ℝ) (Real.pi / 2)
  have hsub : S ⊆ Icc 0 (Real.pi / 2) := inter_subset_right.trans Ioo_subset_Icc_self
  have hmono := (fullTiltedSupportQuarterPair_first_tangent_order
    hU hm.le haffine hρ hρ0 hρK heq hunit).1
  have hB := measurableSet_firstTangentSource hU.isCap.isCompact
  -- The sine-weighted branch mass on `T ⊆ S` is the horizontal source mass on `X '' T`,
  -- which is ordinary length inside the positive niche.
  have hmass (T : Set ℝ) (hT : MeasurableSet T) (hTS : T ⊆ S) :
      (∫⁻ t in T, ENNReal.ofReal (aB t * Real.sin t)) = volume (X '' T) := by
    have himage := hT.image_of_monotoneOn (hmono.mono (hTS.trans hsub))
    have hgraph : ∀ᵐ z ∂(J.measure : Measure Plane), z ∈ firstTangentSource target →
        z.2 = X z.1 := by
      filter_upwards [(ae_restrict_iff' hB).mp (J.ae_first_tangent_source_graph hU hheight
        haffine hTargetBox hleft hright hρ hρ0 hρK heq)] with z hz hb
      exact (hz hb).trans (congrArg Prod.fst (fullTiltedSupportQuarterPair_first_tangency
        hU hm.le haffine hρ hρ0 hρK heq ⟨hb.1.1.le, hb.1.2⟩)).symm
    have hexclusive := J.ae_exclusive_first_source_on_image hU hm.le haffine hρ hρ0 hρK heq
      hl hr hheight hm hleft hright hunit hphase
        fun t ht => ⟨(hTS ht).2, (hTS ht).1.1, (hTS ht).1.2.2.1⟩
    have hsubX : X '' T ⊆ firstUnitPositiveInterval target C := by
      rintro _ ⟨t, ht, rfl⟩
      obtain ⟨⟨-, hx, hpos, hN⟩, -⟩ := hTS ht
      rw [firstUnitPositiveInterval, ← fullTiltedSupportQuarterPair_positive_middle_eq hU hm.le
        haffine hρ hρ0 hρK heq hl hr hC hm hheight hlow hhigh hh hunit]
      exact ⟨hx, hpos.trans_eq hN.symm⟩
    have hdensity := J.sourceBranch_density_sine_eq hU hheight haffine
      hTargetBox hleft hright heq (firstTangentSource target) 0
    simp only [add_zero] at hdensity
    rw [← withDensity_apply _ hT, ← hdensity, ← Measure.restrict_eq_self volume hsubX,
      ← J.horizontalProjection_restrict_firstUnitPositiveInterval_eq_volume hU hl hr hC hm
        hheight haffine hlow hhigh hh hρ hρ0 hρK heq hunit hleft hright,
      Measure.restrict_eq_self _ hsubX]
    simp only [sourceBranchAngular, sub_zero]
    rw [← map_withDensity_comp (J.sourceBranchMeasure (firstTangentSource target))
        measurable_fst Real.measurable_sin.ennreal_ofReal,
      Measure.map_apply measurable_fst hT, sourceBranchMeasure,
      ← restrict_withDensity hB, Measure.restrict_apply (hT.preimage measurable_fst),
      ← J.source_sine_spatial_eq_horizontalProjection, Measure.map_apply measurable_snd himage]
    refine measure_congr ?_
    filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le hgraph,
      (withDensity_absolutelyContinuous _ _).ae_le hexclusive] with z hg he
    exact propext ⟨fun hz => ⟨z.1, hz.1, (hg hz.2).symm⟩, fun hz => (he hz).symm⟩
  have hsin : ∀ᵐ t ∂volume.restrict S, 0 < Real.sin t := by
    filter_upwards [ae_restrict_mem (hc.inter measurableSet_Ioo)] with t ht
    exact Real.sin_pos_of_pos_of_lt_pi ht.2.1 (by linarith [ht.2.2, Real.pi_pos])
  have hweight := ae_weight_eq_deriv_of_monotone_image_mass (hc.inter measurableSet_Ioo)
    (hmono.mono hsub) ((J.measurable_sourceBranchDensity _ _).mul Real.measurable_sin)
    ((measurable_const.sub hρ).mul Real.measurable_sin)
    (hsin.mono fun t hs => mul_nonneg (J.sourceBranchDensity_nonneg _ _ _) hs.le)
    (by filter_upwards [hsin, ae_restrict_of_ae_restrict_of_subset inter_subset_right hunit]
          with t hs hu using mul_nonneg (sub_nonneg.mpr hu) hs.le)
    ((ae_restrict_of_ae_restrict_of_subset inter_subset_right
      (fullTiltedSupportQuarterPair_tangent_calculus hU hm.le haffine hρ hρ0 hρK
        heq).2.2.2.2).mono fun _ ht => ht.1) hmass
  refine (ae_restrict_iff' hc).mp ?_
  rw [Measure.restrict_restrict hc]
  filter_upwards [hweight, hsin] with t he hs using mul_right_cancel₀ hs.ne' he

end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
