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

include hl hr in
private theorem middle_eq : Ioo (horizontalLeft target + capWidth target / 4)
    (horizontalRight target - capWidth target / 4) = Ioo (-C) C := by
  unfold capWidth; rw [hl, hr]; congr 1 <;> ring

include hl hr hC hleft hright in
private theorem Ioo_subset_box : Ioo (-C) C ⊆ Icc a b := fun x hx =>
  ⟨by linarith only [hleft, hl, hx.1, hC], by linarith only [hright, hr, hx.2, hC]⟩

include hU C hl hr hC hleft hright in
theorem ae_hasDerivAt_niche_on_source :
    ∀ᵐ z ∂(J.measure : Measure Plane),
      HasDerivAt (sweptNiche target (Real.pi / 2)) (J.nicheDerivative z.2) z.2 := by
  have hmid := middle_eq hl hr
  have hd := (ae_restrict_iff' measurableSet_Ioo).mp
    (J.ae_hasDerivAt_niche hU.isCap (Ioo_subset_box hl hr hC hleft hright) hmid.ge)
  filter_upwards [J.ae_spatial_mem_open_middle hU.isCap, ae_of_ae_map measurable_snd.aemeasurable
    (J.spatial_marginal_absolutelyContinuous.ae_le hd)] with z hz hd
  exact hd (hmid ▸ hz)

include hU hl hr hC hm hheight haffine hlow hhigh hh hρ hρ0 hρK heq hunit hleft hright in
theorem setIntegral_sourceGraphResidual_eq_zero {E : Set ℝ} (hE : MeasurableSet E) :
    (∫ z in univ ×ˢ E, J.sourceGraphResidual z ∂(J.measure : Measure Plane)) = 0 := by
  have hmid := middle_eq hl hr
  have hP := fullTiltedSupportQuarterPair_positive_middle_eq hU hm.le haffine hρ hρ0 hρK heq hl hr
    hC hm hheight hlow hhigh hh hunit
  have hs : univ ×ˢ E =ᵐ[(J.measure : Measure Plane)]
      univ ×ˢ (E ∩ firstUnitPositiveInterval target C) := by
    filter_upwards [J.ae_spatial_mem_open_middle hU.isCap, J.ae_niche_pos_of_first_unit hU hl hr hC
      hm hheight haffine hlow hhigh hh hρ hρ0 hρK heq hunit] with z hz hp
    have : z.2 ∈ firstUnitPositiveInterval target C := hP.le ⟨hmid ▸ hz, hp⟩
    simp [this]
  rw [setIntegral_congr_set hs]
  exact J.setIntegral_graph_residual_eq_zero hU.isCap
    (fun x hx => Ioo_subset_box hl hr hC hleft hright (hP.ge hx).1)
    (fun x hx => hmid.ge (hP.ge hx).1) (fun x hx => (hP.ge hx).2) (hE.inter measurableSet_Ioo)
    inter_subset_right

include hU hl hr hC hm hheight haffine hlow hhigh hh hρ hρ0 hρK heq hunit hTargetBox hleft hright in
theorem setIntegral_corner_residuals_add_eq_zero {E : Set ℝ} (hE : MeasurableSet E) :
    (∫ z in univ ×ˢ E, J.sourceGraphResidual z
      ∂J.sourceBranchMeasure (firstCornerSource target)) +
      (∫ z in univ ×ˢ E, J.sourceGraphResidual z
        ∂J.sourceBranchMeasure (secondCornerSource target)) = 0 := by
  have hd := J.ae_hasDerivAt_niche_on_source hU hl hr hC hleft hright
  have hz₁ : ∀ᵐ z ∂J.sourceBranchMeasure (firstTangentSource target),
      J.sourceGraphResidual z = 0 := by
    filter_upwards [ae_restrict_mem (measurableSet_firstTangentSource hU.isCap.isCompact),
      J.ae_first_tangent_source_contact hU hheight haffine hTargetBox hleft hright hρ hρ0 hρK heq,
      ae_restrict_of_ae (J.ae_first_wall_contact hU.isCap), ae_restrict_of_ae hd]
      with z hz hreg hc hd
    rw [sourceGraphResidual, hU.isCap.niche_derivative_at_strict_first_contact hreg.1.1 hd
      (hc hz.1).1 hz.2, div_mul_cancel₀ _ (Real.sin_pos_of_pos_of_lt_pi hz.1.1
        (by linarith only [hz.1.2, Real.pi_pos])).ne', neg_add_cancel]
  have hz₂ : ∀ᵐ z ∂J.sourceBranchMeasure (secondTangentSource target),
      J.sourceGraphResidual z = 0 := by
    filter_upwards [ae_restrict_mem (measurableSet_secondTangentSource hU.isCap.isCompact),
      J.ae_second_tangent_source_contact hU hheight haffine hTargetBox hleft hright hρ hρ0 hρK heq,
      ae_restrict_of_ae (J.ae_second_wall_contact hU.isCap), ae_restrict_of_ae hd]
      with z hz hreg hc hd
    have hg := hU.isCap.niche_derivative_at_strict_second_contact hreg.1.1 hd (hc hz.1).1 hz.2
    rw [Real.sin_sub_pi_div_two, Real.cos_sub_pi_div_two] at hg
    rw [sourceGraphResidual, hg, div_mul_cancel₀ _ (Real.sin_pos_of_pos_of_lt_pi
      (by linarith only [hz.1.1, Real.pi_pos]) hz.1.2).ne', neg_add_cancel]
  have hi (S : Set Plane) : IntegrableOn J.sourceGraphResidual (univ ×ˢ E)
      (J.sourceBranchMeasure S) :=
    (J.integrable_sourceGraphResidual.mono_measure (J.sourceBranchMeasure_le S)).integrableOn
  have hz := J.setIntegral_sourceGraphResidual_eq_zero hU hl hr hC hm hheight haffine
    hlow hhigh hh hρ hρ0 hρK heq hunit hleft hright hE
  rw [← J.source_four_branch_partition hU.isCap (J.ae_niche_pos_of_first_unit hU hl hr hC hm
      hheight haffine hlow hhigh hh hρ hρ0 hρK heq hunit),
    Measure.restrict_add, Measure.restrict_add, Measure.restrict_add,
    integral_add_measure (integrable_add_measure.mpr ⟨hi _, hi _⟩)
      (integrable_add_measure.mpr ⟨hi _, hi _⟩),
    integral_add_measure (hi _) (hi _), integral_add_measure (hi _) (hi _),
    integral_eq_zero_of_ae (ae_restrict_of_ae hz₁), integral_eq_zero_of_ae (ae_restrict_of_ae hz₂),
    zero_add, zero_add] at hz
  exact hz

end ActualPair
end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
