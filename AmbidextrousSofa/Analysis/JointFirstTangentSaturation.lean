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

theorem measurableSet_firstTangentChargedSet {U : Set Plane} (hU : IsDownwardCap U)
    {C : ℝ} {p : ℝ → ℝ} {B : ℝ → Plane}
    (hp : Measurable p) (hBx : Measurable (fun t => (B t).1))
    (hBy : Measurable (fun t => (B t).2)) :
    MeasurableSet (firstTangentChargedSet U C p B) := by
  have hn : Continuous (fun x => sweptNiche U (Real.pi / 2) x) :=
    continuous_capSweptNiche.comp
      (continuous_const.prodMk continuous_id : Continuous (fun x => (hU.toCompactCap, x)))
  exact (measurableSet_lt hp measurable_const).inter
    ((measurableSet_Ioo.preimage hBx).inter
      ((measurableSet_lt measurable_const hBy).inter
        (measurableSet_eq_fun (hn.measurable.comp hBx) hBy)))

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

theorem fullTiltedSupportQuarterPair_first_tangent_continuous_global :
    Continuous (fun t => (B t).1) ∧ Continuous (fun t => (B t).2) := by
  have hf : Continuous (F).f := hU.isCap.imported_isConvexBody.continuous_supp
  have hfD : Continuous (F).fD := hU.isCap.continuous_closedSupportDerivative hρ hρ0 hρK 0
  constructor <;> dsimp only [firstTangentPoint, Reference.supportPoint] <;> fun_prop

theorem fullTiltedSupportQuarterPair_measurableSet_firstTangentChargedSet (C : ℝ) :
    MeasurableSet (firstTangentChargedSet U C p B) := by
  have hB := fullTiltedSupportQuarterPair_first_tangent_continuous_global
    hU hm haffine hρ hρ0 hρK heq
  exact measurableSet_firstTangentChargedSet hU.isCap
    (fullTiltedSupportQuarterPair_momenta_continuous
      hU hm haffine hρ hρ0 hρK heq).1.measurable hB.1.measurable hB.2.measurable

end ActualPair

namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

theorem first_branch_sine_mass_eq_horizontalProjection
    (hTarget : IsDownwardCap target) {X : ℝ → ℝ} {T : Set ℝ}
    (hT : MeasurableSet T) (himage : MeasurableSet (X '' T))
    (hgraph : ∀ᵐ z ∂J.sourceBranchMeasure (firstTangentSource target), z.2 = X z.1)
    (hexclusive : ∀ᵐ z ∂(J.measure : Measure Plane), z.2 ∈ X '' T →
      z ∈ firstTangentSource target ∧ z.1 ∈ T) :
    ((J.sourceBranchAngular (firstTangentSource target) 0).withDensity
      (fun t => ENNReal.ofReal (Real.sin t))) T =
        (J.horizontalProjection : Measure ℝ) (X '' T) := by
  have hB := measurableSet_firstTangentSource hTarget.isCompact
  have hg : ∀ᵐ z ∂(J.measure : Measure Plane), z ∈ firstTangentSource target →
      z.2 = X z.1 := (ae_restrict_iff' hB).mp hgraph
  simp only [sourceBranchAngular, sub_zero]
  rw [← map_withDensity_comp (J.sourceBranchMeasure (firstTangentSource target))
      measurable_fst Real.measurable_sin.ennreal_ofReal,
    Measure.map_apply measurable_fst hT, sourceBranchMeasure,
    ← restrict_withDensity hB, Measure.restrict_apply (hT.preimage measurable_fst),
    ← J.source_sine_spatial_eq_horizontalProjection,
    Measure.map_apply measurable_snd himage]
  apply measure_congr
  filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le hg,
    (withDensity_absolutelyContinuous _ _).ae_le hexclusive] with z hg he
  apply propext
  constructor
  · intro hz
    exact ⟨z.1, hz.1, (hg hz.2).symm⟩
  · intro hz
    have hc := he hz
    exact ⟨hc.2, hc.1⟩

section ActualTangent

variable (hU : IsFullCapMaximizer target) {C h m c : ℝ}
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

theorem lintegral_first_tangent_density_mul_sin_eq_volume_image {α η : ℝ}
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η)
    {T : Set ℝ} (hT : MeasurableSet T)
    (hgood : ∀ t ∈ T, t ∈ Ioo (0 : ℝ) (Real.pi / 2) ∧ t ∈ charged) :
    (∫⁻ t in T, ENNReal.ofReal (aB t * Real.sin t)) = volume (X '' T) := by
  have horder := (fullTiltedSupportQuarterPair_first_tangent_order
    hU hm.le haffine hρ hρ0 hρK heq hunit).1
  have hmono : MonotoneOn X T := horder.mono
    (fun _ ht => Ioo_subset_Icc_self (hgood _ ht).1)
  have himage : MeasurableSet (X '' T) := hT.image_of_monotoneOn hmono
  have hgraph : ∀ᵐ z ∂J.sourceBranchMeasure (firstTangentSource target), z.2 = X z.1 := by
    filter_upwards [J.ae_first_tangent_source_graph hU hheight haffine hTargetBox
      hleft hright hρ hρ0 hρK heq,
      ae_restrict_mem (measurableSet_firstTangentSource hU.isCap.isCompact)] with z hz hb
    have hmatch := fullTiltedSupportQuarterPair_first_tangency
      hU hm.le haffine hρ hρ0 hρK heq ⟨hb.1.1.le, hb.1.2⟩
    exact hz.trans (congrArg Prod.fst hmatch).symm
  have hexclusive := J.ae_exclusive_first_source_on_image hU hm.le haffine hρ hρ0 hρK heq
    hl hr hheight hm hleft hright hunit hphase
      (fun t ht => ⟨(hgood t ht).1, (hgood t ht).2.1, (hgood t ht).2.2.2.1⟩)
  have hmass := J.first_branch_sine_mass_eq_horizontalProjection hU.isCap
    hT himage hgraph hexclusive
  have hdensity := J.sourceBranch_density_sine_eq hU hheight haffine
    hTargetBox hleft hright heq (firstTangentSource target) 0
  have hdensity' : (J.sourceBranchAngular (firstTangentSource target) 0).withDensity
      (fun t => ENNReal.ofReal (Real.sin t)) =
        volume.withDensity (fun t => ENNReal.ofReal (aB t * Real.sin t)) := by
    simpa only [add_zero] using hdensity
  rw [hdensity', withDensity_apply _ hT] at hmass
  have hpositiveSet := fullTiltedSupportQuarterPair_positive_middle_eq hU hm.le haffine
    hρ hρ0 hρK heq hl hr hC hm hheight hlow hhigh hh hunit
  have hsub : X '' T ⊆ firstUnitPositiveInterval target C := by
    rintro x ⟨t, ht, rfl⟩
    change X t ∈ Ioo (max (-C) (companionZero (leftCompanionCap target (-C)))) C
    rw [← hpositiveSet]
    have hc := (hgood t ht).2
    refine ⟨hc.2.1, ?_⟩
    rw [hc.2.2.2]
    exact hc.2.2.1
  have hH := congrArg (fun μ : Measure ℝ => μ (X '' T))
    (J.horizontalProjection_restrict_firstUnitPositiveInterval_eq_volume
      hU hl hr hC hm hheight haffine hlow hhigh hh hρ hρ0 hρK heq hunit hleft hright)
  have hHeq : (J.horizontalProjection : Measure ℝ) (X '' T) = volume (X '' T) := by
    simpa only [Measure.restrict_apply himage, inter_eq_left.mpr hsub] using hH
  exact hmass.trans hHeq

theorem ae_first_tangent_density_eq_one_sub_on_charged {α η : ℝ}
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      t ∈ charged → aB t = 1 - ρ t := by
  let S : Set ℝ := Ioo (0 : ℝ) (Real.pi / 2) ∩ charged
  have hS : MeasurableSet S := measurableSet_Ioo.inter
    (fullTiltedSupportQuarterPair_measurableSet_firstTangentChargedSet
      hU hm.le haffine hρ hρ0 hρK heq C)
  have hsub : S ⊆ Ioo (0 : ℝ) (Real.pi / 2) := inter_subset_left
  have hmono : MonotoneOn X S :=
    (fullTiltedSupportQuarterPair_first_tangent_order
      hU hm.le haffine hρ hρ0 hρK heq hunit).1.mono
        (hsub.trans Ioo_subset_Icc_self)
  obtain ⟨_hBx, _hBy, _hDx, _hDy, hderiv⟩ :=
    fullTiltedSupportQuarterPair_tangent_calculus hU hm.le haffine hρ hρ0 hρK heq
  have hD : ∀ᵐ t ∂volume.restrict S,
      HasDerivAt X ((1 - ρ t) * Real.sin t) t :=
    (ae_restrict_of_ae_restrict_of_subset hsub hderiv).mono (fun _ ht => ht.1)
  have hw0 : ∀ᵐ t ∂volume.restrict S, 0 ≤ aB t * Real.sin t := by
    filter_upwards [ae_restrict_mem hS] with t ht
    exact mul_nonneg (J.sourceBranchDensity_nonneg _ _ _)
      (Real.sin_pos_of_pos_of_lt_pi ht.1.1
        (by linarith only [ht.1.2, Real.pi_pos])).le
  have hD0 : ∀ᵐ t ∂volume.restrict S, 0 ≤ (1 - ρ t) * Real.sin t := by
    filter_upwards [ae_restrict_mem hS,
      ae_restrict_of_ae_restrict_of_subset hsub hunit] with t ht hu
    exact mul_nonneg (sub_nonneg.mpr hu)
      (Real.sin_pos_of_pos_of_lt_pi ht.1.1
        (by linarith only [ht.1.2, Real.pi_pos])).le
  have heqWeight := ae_weight_eq_deriv_of_monotone_image_mass hS hmono
    ((J.measurable_sourceBranchDensity _ _).mul Real.measurable_sin)
    ((measurable_const.sub hρ).mul Real.measurable_sin) hw0 hD0 hD
      (fun T hT hTS => J.lintegral_first_tangent_density_mul_sin_eq_volume_image
        hU hl hr hC hm hheight haffine hlow hhigh hh hρ hρ0 hρK heq hunit
        hTargetBox hleft hright hphase hT (fun t ht => hTS ht))
  have hglobal := (ae_restrict_iff' hS).mp heqWeight
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hglobal] with t ht he
  intro hc
  have hs : Real.sin t ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith only [ht.2, Real.pi_pos])).ne'
  exact (mul_right_cancel₀ hs) (he ⟨ht, hc⟩)

end ActualTangent
end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
