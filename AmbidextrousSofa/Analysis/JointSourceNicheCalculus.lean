module

public import AmbidextrousSofa.Analysis.JointBranchDensity
public import AmbidextrousSofa.Analysis.JointSourceAffine
public import AmbidextrousSofa.Analysis.JointNicheDerivative
public import AmbidextrousSofa.Analysis.ContactGraphSlope

@[expose] public section

/-!
# The common niche derivative on every actual source branch

The actual first-unit geometry identifies one open positive niche
interval. The joint measure is concentrated on that interval, so the
spatial graph residual cancels against every measurable spatial test.
At both strict tangent branches the residual vanishes separately.
Consequently the two corner restrictions carry exactly opposite
residual fluxes.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

def firstUnitPositiveInterval (U : Set Plane) (C : ℝ) : Set ℝ :=
  Ioo (max (-C) (companionZero (leftCompanionCap U (-C)))) C

namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

def sourceGraphResidual (z : Plane) : ℝ :=
  J.nicheDerivative z.2 * Real.sin z.1 + Real.cos z.1

theorem measurable_sourceGraphResidual : Measurable J.sourceGraphResidual :=
  ((J.measurable_nicheDerivative.comp measurable_snd).mul
    (Real.measurable_sin.comp measurable_fst)).add
      (Real.measurable_cos.comp measurable_fst)

theorem integrable_sourceGraphResidual :
    Integrable J.sourceGraphResidual (J.measure : Measure Plane) :=
  (J.integrable_spatial_sine J.integrable_nicheDerivative).add
    (sourceCosineFunction.integrable _)

section ActualPair

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

theorem ae_spatial_mem_firstUnitPositiveInterval :
    ∀ᵐ z ∂(J.measure : Measure Plane), z.2 ∈ firstUnitPositiveInterval target C := by
  have hmid : Ioo (horizontalLeft target + capWidth target / 4)
      (horizontalRight target - capWidth target / 4) = Ioo (-C) C := by
    unfold capWidth
    rw [hl, hr]
    congr 1 <;> ring
  have hpositive := fullTiltedSupportQuarterPair_positive_middle_eq hU hm.le haffine
    hρ hρ0 hρK heq hl hr hC hm hheight hlow hhigh hh hunit
  filter_upwards [J.ae_spatial_mem_open_middle hU.isCap,
    J.ae_niche_pos_of_first_unit hU hl hr hC hm hheight haffine hlow hhigh hh
      hρ hρ0 hρK heq hunit] with z hz hp
  rw [hmid] at hz
  change z.2 ∈ Ioo (max (-C) (companionZero (leftCompanionCap target (-C)))) C
  rw [← hpositive]
  exact ⟨hz, hp⟩

theorem ae_hasDerivAt_niche_on_source :
    ∀ᵐ z ∂(J.measure : Measure Plane),
      HasDerivAt (sweptNiche target (Real.pi / 2)) (J.nicheDerivative z.2) z.2 := by
  have hmid : Ioo (horizontalLeft target + capWidth target / 4)
      (horizontalRight target - capWidth target / 4) = Ioo (-C) C := by
    unfold capWidth
    rw [hl, hr]
    congr 1 <;> ring
  have hbox : Ioo (-C) C ⊆ Icc a b := by
    intro x hx
    have hla : a < -2 * C := by simpa only [hl] using hleft
    have hrb : 2 * C < b := by simpa only [hr] using hright
    constructor <;> linarith only [hla, hrb, hx.1, hx.2, hC]
  have hd := J.ae_hasDerivAt_niche hU.isCap hbox (by rw [hmid])
  have hglobal := (ae_restrict_iff' measurableSet_Ioo).mp hd
  have hpull := ae_of_ae_map measurable_snd.aemeasurable
    (J.spatial_marginal_absolutelyContinuous.ae_le hglobal)
  filter_upwards [J.ae_spatial_mem_open_middle hU.isCap, hpull] with z hz hd
  rw [hmid] at hz
  exact hd hz

theorem setIntegral_sourceGraphResidual_eq_zero {E : Set ℝ} (hE : MeasurableSet E) :
    (∫ z in univ ×ˢ E, J.sourceGraphResidual z ∂(J.measure : Measure Plane)) = 0 := by
  let P := firstUnitPositiveInterval target C
  have hP : MeasurableSet P := measurableSet_Ioo
  have hmid : Ioo (horizontalLeft target + capWidth target / 4)
      (horizontalRight target - capWidth target / 4) = Ioo (-C) C := by
    unfold capWidth
    rw [hl, hr]
    congr 1 <;> ring
  have hsub : P ⊆ Ioo (-C) C := fun _ hx =>
    ⟨(le_max_left _ _).trans_lt hx.1, hx.2⟩
  have hbox : P ⊆ Icc a b := by
    intro x hx
    have hla : a < -2 * C := by simpa only [hl] using hleft
    have hrb : 2 * C < b := by simpa only [hr] using hright
    have hx' := hsub hx
    constructor <;> linarith only [hla, hrb, hx'.1, hx'.2, hC]
  have hpos : ∀ x ∈ P, 0 < sweptNiche target (Real.pi / 2) x := by
    intro x hx
    exact (fullTiltedSupportQuarterPair_positive_middle_iff hU hm.le haffine
      hρ hρ0 hρK heq hl hr hC hm hheight hlow hhigh hh hunit (hsub hx)).mpr
        ((le_max_right _ _).trans_lt hx.1)
  have hs : univ ×ˢ E =ᵐ[(J.measure : Measure Plane)] univ ×ˢ (E ∩ P) := by
    filter_upwards [J.ae_spatial_mem_firstUnitPositiveInterval hU hl hr hC hm hheight
      haffine hlow hhigh hh hρ hρ0 hρK heq hunit] with z hz
    apply propext
    simp only [mem_prod, mem_univ, true_and, mem_inter_iff, hz, and_true]
  rw [setIntegral_congr_set hs]
  exact J.setIntegral_graph_residual_eq_zero hU.isCap hbox
    (by rw [hmid]; exact hsub) hpos (hE.inter hP) inter_subset_right

theorem ae_first_tangent_residual_eq_zero :
    ∀ᵐ z ∂J.sourceBranchMeasure (firstTangentSource target), J.sourceGraphResidual z = 0 := by
  filter_upwards [ae_restrict_mem (measurableSet_firstTangentSource hU.isCap.isCompact),
    J.ae_first_tangent_source_contact hU hheight haffine hTargetBox hleft hright
      hρ hρ0 hρK heq,
    ae_restrict_of_ae (J.ae_first_wall_contact hU.isCap),
    ae_restrict_of_ae (J.ae_hasDerivAt_niche_on_source hU hl hr hC hleft hright)]
    with z hz hreg hc hd
  have hg := hU.isCap.niche_derivative_at_strict_first_contact hreg.1.1 hd
    (hc hz.1).1 hz.2
  have hs : Real.sin z.1 ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hz.1.1
    (by linarith only [hz.1.2, Real.pi_pos])).ne'
  unfold sourceGraphResidual
  rw [hg]
  field_simp [hs]
  ring

theorem ae_second_tangent_residual_eq_zero :
    ∀ᵐ z ∂J.sourceBranchMeasure (secondTangentSource target), J.sourceGraphResidual z = 0 := by
  filter_upwards [ae_restrict_mem (measurableSet_secondTangentSource hU.isCap.isCompact),
    J.ae_second_tangent_source_contact hU hheight haffine hTargetBox hleft hright
      hρ hρ0 hρK heq,
    ae_restrict_of_ae (J.ae_second_wall_contact hU.isCap),
    ae_restrict_of_ae (J.ae_hasDerivAt_niche_on_source hU hl hr hC hleft hright)]
    with z hz hreg hc hd
  have hg := hU.isCap.niche_derivative_at_strict_second_contact hreg.1.1 hd
    (hc hz.1).1 hz.2
  have hc0 : Real.cos (z.1 - Real.pi / 2) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith only [hreg.1.1.1, Real.pi_pos], hreg.1.1.2⟩).ne'
  have hs : Real.sin z.1 = Real.cos (z.1 - Real.pi / 2) := by
    nth_rw 1 [show z.1 = (z.1 - Real.pi / 2) + Real.pi / 2 by ring]
    exact Real.sin_add_pi_div_two _
  have hc' : Real.cos z.1 = -Real.sin (z.1 - Real.pi / 2) := by
    nth_rw 1 [show z.1 = (z.1 - Real.pi / 2) + Real.pi / 2 by ring]
    exact Real.cos_add_pi_div_two _
  unfold sourceGraphResidual
  rw [hg, hs, hc']
  field_simp [hc0]
  ring

theorem setIntegral_corner_residuals_add_eq_zero {E : Set ℝ} (hE : MeasurableSet E) :
    (∫ z in univ ×ˢ E, J.sourceGraphResidual z
      ∂J.sourceBranchMeasure (firstCornerSource target)) +
      (∫ z in univ ×ˢ E, J.sourceGraphResidual z
        ∂J.sourceBranchMeasure (secondCornerSource target)) = 0 := by
  have hpositive := J.ae_niche_pos_of_first_unit hU hl hr hC hm hheight haffine hlow hhigh hh
    hρ hρ0 hρK heq hunit
  have hsplit := J.source_four_branch_partition hU.isCap hpositive
  have hz := J.setIntegral_sourceGraphResidual_eq_zero hU hl hr hC hm hheight haffine
    hlow hhigh hh hρ hρ0 hρK heq hunit hleft hright hE
  have hi (S : Set Plane) : IntegrableOn J.sourceGraphResidual (univ ×ˢ E)
      (J.sourceBranchMeasure S) :=
    (J.integrable_sourceGraphResidual.mono_measure (J.sourceBranchMeasure_le S)).integrableOn
  have hz₁ : (∫ z in univ ×ˢ E, J.sourceGraphResidual z
      ∂J.sourceBranchMeasure (firstTangentSource target)) = 0 := by
    apply integral_eq_zero_of_ae
    exact ae_restrict_of_ae (J.ae_first_tangent_residual_eq_zero hU hl hr hC hheight
      haffine hρ hρ0 hρK heq hTargetBox hleft hright)
  have hz₂ : (∫ z in univ ×ˢ E, J.sourceGraphResidual z
      ∂J.sourceBranchMeasure (secondTangentSource target)) = 0 := by
    apply integral_eq_zero_of_ae
    exact ae_restrict_of_ae (J.ae_second_tangent_residual_eq_zero hU hl hr hC hheight
      haffine hρ hρ0 hρK heq hTargetBox hleft hright)
  rw [← hsplit, Measure.restrict_add, Measure.restrict_add, Measure.restrict_add,
    integral_add_measure (integrable_add_measure.mpr ⟨hi _, hi _⟩)
      (integrable_add_measure.mpr ⟨hi _, hi _⟩),
    integral_add_measure (hi _) (hi _), integral_add_measure (hi _) (hi _), hz₁, hz₂,
    zero_add, zero_add] at hz
  exact hz

end ActualPair
end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
