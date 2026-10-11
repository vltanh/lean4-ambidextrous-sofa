module

public import AmbidextrousSofa.Analysis.JointCoreSourceGeometry
public import AmbidextrousSofa.Measure.GraphMeasureTransfer

@[expose] public section

/-!
# One corner flux balance for the two literal corner densities

The two signed residuals are integrable because they are restrictions
of the actual common graph residual. Their spatial test identities
pull back along the strictly decreasing core coordinate. Multiplying
the resulting angular cancellation by the actual corner speed uses
the two contact cofactors and gives `p * aZ + q * aW = 0`.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

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
local notation "Z" => innerCornerPoint (F).f (F).g
set_option quotPrecheck false in
local notation "p" => supportP (F).fD (F).g
set_option quotPrecheck false in
local notation "q" => supportQ (F).gD (F).f
set_option quotPrecheck false in
local notation "X" => (fun t => (Z t).1)
local notation "XD" => (fun t => p t * Real.cos t - q t * Real.sin t)
local notation "R₁" => (fun t => J.nicheDerivative (X t) * Real.sin t + Real.cos t)
local notation "R₂" => (fun t => J.nicheDerivative (X t) * Real.cos t - Real.sin t)
local notation "aZ" => J.sourceBranchDensity (firstCornerSource target) 0
local notation "aW" => J.sourceBranchDensity (secondCornerSource target) (Real.pi / 2)

include hl hr hC hheight hlow hhigh hh hunit hTargetBox hleft hright in
theorem ae_corner_density_zero_off_core {α η : ℝ}
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) :
    ∀ᵐ t ∂volume, t ∉ Ioo α η → aZ t = 0 ∧ aW t = 0 := by
  have hfirst : ∀ᵐ z ∂J.sourceBranchMeasure (firstCornerSource target), z.1 - 0 ∈ Ioo α η :=
    (J.ae_first_corner_core_geometry hU hl hr hC hm hheight haffine hlow hhigh hh hρ hρ0 hρK
      heq hunit hleft hright hphase).mono fun z hz => by simpa only [sub_zero] using hz.1
  filter_upwards [J.ae_sourceBranch_property hU hheight haffine hTargetBox hleft hright heq
    measurableSet_Ioo hfirst, J.ae_sourceBranch_property hU hheight haffine hTargetBox hleft
      hright heq measurableSet_Ioo ((J.ae_second_corner_core_geometry hU hl hr hC hm hheight
        haffine hlow hhigh hh hρ hρ0 hρK heq hunit hleft hright hphase).mono fun z hz => hz.1)]
    with t hZ hW ht using ⟨not_imp_comm.1 hZ ht, not_imp_comm.1 hW ht⟩

include hl hr hC hheight hlow hhigh hh hunit hTargetBox hleft hright in
theorem ae_corner_density_balance {α η : ℝ}
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      p t * aZ t + q t * aW t = 0 := by
  have hX := (fullTiltedSupportQuarterPair_core_continuous_global
    hU hm.le haffine hρ hρ0 hρK heq).1
  have hpq := fullTiltedSupportQuarterPair_momenta_continuous
    hU hm.le haffine hρ hρ0 hρK heq
  have hXD : Measurable XD := (hpq.1.measurable.mul Real.measurable_cos).sub
    (hpq.2.measurable.mul Real.measurable_sin)
  have hR₁ : Measurable R₁ := ((J.measurable_nicheDerivative.comp hX.measurable).mul
    Real.measurable_sin).add Real.measurable_cos
  have hR₂ : Measurable R₂ := ((J.measurable_nicheDerivative.comp hX.measurable).mul
    Real.measurable_cos).sub Real.measurable_sin
  have hgeom₁ := J.ae_first_corner_core_geometry hU hl hr hC hm hheight haffine
    hlow hhigh hh hρ hρ0 hρK heq hunit hleft hright hphase
  have hgeom₂ := J.ae_second_corner_core_geometry hU hl hr hC hm hheight haffine
    hlow hhigh hh hρ hρ0 hρK heq hunit hleft hright hphase
  have hzero := J.ae_corner_density_zero_off_core hU hl hr hC hm hheight haffine
    hlow hhigh hh hρ hρ0 hρK heq hunit hTargetBox hleft hright hphase
  -- The spatial cancellation of the two residuals pulls back to the core angles.
  have hres₁ : ∀ᵐ z ∂J.sourceBranchMeasure (firstCornerSource target),
      J.sourceGraphResidual z = R₁ (z.1 - 0) := by
    filter_upwards [hgeom₁] with z hz
    simp only [sourceGraphResidual, sub_zero, hz.2.1]
  have hres₂ : ∀ᵐ z ∂J.sourceBranchMeasure (secondCornerSource target),
      J.sourceGraphResidual z = R₂ (z.1 - Real.pi / 2) := by
    filter_upwards [hgeom₂] with z hz
    simp only [sourceGraphResidual, hz.2.1, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two,
      sub_neg_eq_add]
  have hcore {f : ℝ → ℝ} {E : Set ℝ} (hE : MeasurableSet E)
      (hf : ∀ᵐ t ∂volume, t ∉ Ioo α η → f t = 0) :
      ∫ t in X ⁻¹' E, f t = ∫ t in Ioo α η ∩ X ⁻¹' E, f t :=
    setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (hX.measurable hE).nullMeasurableSet
      inter_subset_right (hf.mono fun t ht hs => ht fun hc => hs.2 ⟨hc, hs.1⟩)
  have hcancel := ae_add_eq_zero_on_of_graph_setIntegral_eq_zero measurableSet_Ioo
    hX.continuousOn (fullTiltedSupportQuarterPair_core_strictAntiOn_open
      hU hm.le haffine hρ hρ0 hρK heq hphase).injOn
    (J.integrable_sourceBranchDensity_mul_of_ae_eq hU hheight haffine hTargetBox hleft hright
      heq hR₁ (J.integrable_sourceGraphResidual.mono_measure (J.sourceBranchMeasure_le _))
      hres₁).integrableOn
    (J.integrable_sourceBranchDensity_mul_of_ae_eq hU hheight haffine hTargetBox hleft hright
      heq hR₂ (J.integrable_sourceGraphResidual.mono_measure (J.sourceBranchMeasure_le _))
      hres₂).integrableOn fun E hE => by
    have htest := J.setIntegral_corner_residuals_add_eq_zero hU hl hr hC hm hheight haffine
      hlow hhigh hh hρ hρ0 hρK heq hunit hTargetBox hleft hright hE
    rwa [J.setIntegral_sourceBranch_eq_graph hU hheight haffine hTargetBox hleft hright heq
      hX.measurable hR₁ (hgeom₁.mono fun z hz => by simpa only [sub_zero] using hz.2.1) hres₁ hE,
      J.setIntegral_sourceBranch_eq_graph hU hheight haffine hTargetBox hleft hright heq
        hX.measurable hR₂ (hgeom₂.mono fun z hz => hz.2.1) hres₂ hE,
      hcore hE (hzero.mono fun t ht hn => by rw [(ht hn).1, zero_mul]),
      hcore hE (hzero.mono fun t ht hn => by rw [(ht hn).2, zero_mul])] at htest
  -- Multiplying by the corner speed uses the two contact cofactors.
  filter_upwards [ae_restrict_of_ae (J.ae_sourceBranchDensity_mul_eq hU hheight haffine
      hTargetBox hleft hright heq (d := 0) (f := fun t => R₁ t * XD t) (hR₁.mul hXD)
      hpq.1.measurable (hgeom₁.mono fun z hz => by simpa only [sub_zero] using hz.2.2)),
    ae_restrict_of_ae (J.ae_sourceBranchDensity_mul_eq hU hheight haffine hTargetBox hleft
      hright heq (f := fun t => R₂ t * XD t) (hR₂.mul hXD) hpq.2.measurable
      (hgeom₂.mono fun z hz => hz.2.2)),
    ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Ioo).mp hcancel),
    ae_restrict_of_ae hzero] with t h₁ h₂ hcancel hzero
  by_cases ht : t ∈ Ioo α η
  · linear_combination (p t * Real.cos t - q t * Real.sin t) * hcancel ht - h₁ - h₂
  · simp [(hzero ht).1, (hzero ht).2]

end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
