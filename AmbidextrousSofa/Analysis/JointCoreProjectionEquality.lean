import AmbidextrousSofa.Analysis.JointCoreFlux
import AmbidextrousSofa.Analysis.JointCoreProjection

/-!
# Exact core projection at uniquely exposed corner points

The common core projection is the sum of the two literal corner
restrictions, with the original sine weight. Its angular expression
uses the sum of both corner densities. Above the image of any set of
uniquely exposed core contacts, every actual source tag belongs to one
of those corner restrictions; the core projection therefore equals
the full horizontal projection on that image.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa
namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

def coreSourceProjection : Measure ℝ :=
  ((J.sourceBranchMeasure (firstCornerSource target ∪ secondCornerSource target)).withDensity
    (fun z => ENNReal.ofReal (Real.sin z.1))).map Prod.snd

theorem source_sine_spatial_eq_horizontalProjection :
    ((J.measure : Measure Plane).withDensity
      (fun z => ENNReal.ofReal (Real.sin z.1))).map Prod.snd =
        (J.horizontalProjection : Measure ℝ) := by
  rw [horizontalProjection, sourceHorizontalProjection, FiniteMeasure.toMeasure_map,
    weightedFiniteMeasure_toMeasure]
  rfl

theorem coreSourceProjection_restrict_eq_of_source_support
    (hTarget : IsDownwardCap target) {E : Set ℝ} (hE : MeasurableSet E)
    (hsource : ∀ᵐ z ∂(J.measure : Measure Plane), z.2 ∈ E →
      z ∈ firstCornerSource target ∪ secondCornerSource target) :
    J.coreSourceProjection.restrict E = (J.horizontalProjection : Measure ℝ).restrict E := by
  rw [coreSourceProjection, ← J.source_sine_spatial_eq_horizontalProjection,
    Measure.restrict_map measurable_snd hE, Measure.restrict_map measurable_snd hE]
  apply congrArg (fun μ : Measure Plane => μ.map Prod.snd)
  rw [restrict_withDensity (hE.preimage measurable_snd),
    restrict_withDensity (hE.preimage measurable_snd)]
  apply congrArg (fun μ : Measure Plane => μ.withDensity
    (fun z => ENNReal.ofReal (Real.sin z.1)))
  rw [sourceBranchMeasure, Measure.restrict_restrict (hE.preimage measurable_snd)]
  apply Measure.restrict_congr_set
  filter_upwards [hsource] with z hz
  apply propext
  constructor
  · exact fun ht => ht.1
  · exact fun ht => ⟨ht, hz ht⟩

section ActualCore

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
local notation "Z" => innerCornerPoint F.f F.g
local notation "p" => supportP F.fD F.g
local notation "q" => supportQ F.gD F.f
local notation "X" => (fun t => (Z t).1)
local notation "aZ" => J.sourceBranchDensity (firstCornerSource target) 0
local notation "aW" => J.sourceBranchDensity (secondCornerSource target) (Real.pi / 2)
local notation "w" => (fun t => aZ t * Real.sin t + aW t * Real.cos t)

theorem coreSourceProjection_eq_density_graph {α η : ℝ}
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) :
    J.coreSourceProjection =
      ((volume.restrict (Ioo α η)).withDensity (fun t => ENNReal.ofReal (w t))).map X := by
  have hX := (fullTiltedSupportQuarterPair_core_continuous_global
    hU hm.le haffine hρ hρ0 hρK heq).1.measurable
  have hfirst : ∀ᵐ z ∂J.sourceBranchMeasure (firstCornerSource target),
      z.2 = X (z.1 - 0) := by
    filter_upwards [J.ae_first_corner_core_geometry hU hl hr hC hm hheight haffine hlow
      hhigh hh hρ hρ0 hρK heq hunit hleft hright hphase] with z hz
    simpa only [sub_zero] using hz.2.1
  have hsecond : ∀ᵐ z ∂J.sourceBranchMeasure (secondCornerSource target),
      z.2 = X (z.1 - Real.pi / 2) := by
    filter_upwards [J.ae_second_corner_core_geometry hU hl hr hC hm hheight haffine hlow
      hhigh hh hρ hρ0 hρK heq hunit hleft hright hphase] with z hz
    exact hz.2.1
  have hmap₁ : ((J.sourceBranchMeasure (firstCornerSource target)).withDensity
      (fun z => ENNReal.ofReal (Real.sin z.1))).map Prod.snd =
        (volume.withDensity (fun t => ENNReal.ofReal (aZ t * Real.sin t))).map X := by
    have hgraph := graph_weighted_map_eq (measurable_fst.sub_const 0) hX
      (Real.measurable_sin.comp (measurable_id.add_const 0)).ennreal_ofReal hfirst
    change _ = ((J.sourceBranchAngular (firstCornerSource target) 0).withDensity
      (fun t => ENNReal.ofReal (Real.sin (t + 0)))).map X at hgraph
    rw [J.sourceBranch_density_sine_eq hU hheight haffine hTargetBox hleft hright heq] at hgraph
    simpa only [sub_add_cancel, add_zero] using hgraph
  have hmap₂ : ((J.sourceBranchMeasure (secondCornerSource target)).withDensity
      (fun z => ENNReal.ofReal (Real.sin z.1))).map Prod.snd =
        (volume.withDensity (fun t => ENNReal.ofReal (aW t * Real.cos t))).map X := by
    have hgraph := graph_weighted_map_eq (measurable_fst.sub_const (Real.pi / 2)) hX
      (Real.measurable_sin.comp (measurable_id.add_const (Real.pi / 2))).ennreal_ofReal hsecond
    change _ = ((J.sourceBranchAngular (secondCornerSource target) (Real.pi / 2)).withDensity
      (fun t => ENNReal.ofReal (Real.sin (t + Real.pi / 2)))).map X at hgraph
    rw [J.sourceBranch_density_sine_eq hU hheight haffine hTargetBox hleft hright heq] at hgraph
    simpa only [sub_add_cancel, Real.sin_add_pi_div_two] using hgraph
  have hz := J.ae_corner_density_zero_off_core hU hl hr hC hm hheight haffine
    hlow hhigh hh hρ hρ0 hρK heq hunit hTargetBox hleft hright hphase
  have hweights : ∀ᵐ t ∂volume, 0 ≤ aZ t * Real.sin t ∧ 0 ≤ aW t * Real.cos t := by
    filter_upwards [hz] with t ht
    by_cases hc : t ∈ Ioo α η
    · have htq : t ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨hphase.first_mem.1.trans hc.1, hc.2.trans hphase.second_mem.2⟩
      exact ⟨mul_nonneg (J.sourceBranchDensity_nonneg _ _ _)
        (Real.sin_pos_of_pos_of_lt_pi htq.1 (by linarith only [htq.2, Real.pi_pos])).le,
        mul_nonneg (J.sourceBranchDensity_nonneg _ _ _)
          (Real.cos_pos_of_mem_Ioo ⟨by linarith only [htq.1, Real.pi_pos], htq.2⟩).le⟩
    · rw [(ht hc).1, (ht hc).2, zero_mul, zero_mul]
      exact ⟨le_rfl, le_rfl⟩
  have hsum : volume.withDensity (fun t => ENNReal.ofReal (aZ t * Real.sin t)) +
      volume.withDensity (fun t => ENNReal.ofReal (aW t * Real.cos t)) =
        volume.withDensity (fun t => ENNReal.ofReal (w t)) := by
    rw [← withDensity_add_left
      ((J.measurable_sourceBranchDensity _ _).mul Real.measurable_sin).ennreal_ofReal]
    apply withDensity_congr_ae
    filter_upwards [hweights] with t ht
    exact (ENNReal.ofReal_add ht.1 ht.2).symm
  have hrestrict : (volume.restrict (Ioo α η)).withDensity (fun t => ENNReal.ofReal (w t)) =
      volume.withDensity (fun t => ENNReal.ofReal (w t)) := by
    rw [← withDensity_indicator measurableSet_Ioo]
    apply withDensity_congr_ae
    filter_upwards [hz] with t ht
    by_cases hc : t ∈ Ioo α η
    · simp only [indicator_of_mem hc]
    · simp only [indicator_of_not_mem hc, (ht hc).1, (ht hc).2, zero_mul, zero_add,
        ENNReal.ofReal_zero]
  rw [coreSourceProjection, sourceBranchMeasure,
    Measure.restrict_union (disjoint_sourceSlices.mono inter_subset_left inter_subset_left)
      (measurableSet_secondCornerSource hU.isCap.isCompact),
    withDensity_add_measure, Measure.map_add _ _ measurable_snd]
  change ((J.sourceBranchMeasure (firstCornerSource target)).withDensity
    (fun z => ENNReal.ofReal (Real.sin z.1))).map Prod.snd +
      ((J.sourceBranchMeasure (secondCornerSource target)).withDensity
        (fun z => ENNReal.ofReal (Real.sin z.1))).map Prod.snd = _
  rw [hmap₁, hmap₂, ← Measure.map_add _ _ hX, hsum, hrestrict]

theorem ae_sources_over_unique_core_image {T : Set ℝ}
    (hunique : ∀ t ∈ T, ∀ s ∈ Icc (0 : ℝ) (Real.pi / 2),
      fullWallClip hU.isCap.toCompactCap (X t) s = sweptNiche target (Real.pi / 2) (X t) → s = t) :
    ∀ᵐ z ∂(J.measure : Measure Plane), z.2 ∈ X '' T →
      z ∈ firstCornerSource target ∪ secondCornerSource target := by
  filter_upwards [J.ae_sourceQuarterAngle_mem, J.ae_angle_mem_upper,
    J.ae_angle_ne (Real.pi / 2),
    J.ae_sourceQuarterAngle_gt_affine hU hl hr hC hm hheight haffine hlow hhigh hh
      hρ hρ0 hρK heq hunit,
    J.ae_first_wall_contact hU.isCap, J.ae_second_wall_contact hU.isCap]
    with z hquarter hupper htop hafter hfirst hsecond
  rintro ⟨t, ht, hxt⟩
  have hcontact : fullWallClip hU.isCap.toCompactCap z.2 (sourceQuarterAngle z.1) =
      sweptNiche target (Real.pi / 2) z.2 := by
    by_cases hfamily : z.1 < Real.pi / 2
    · simpa only [sourceQuarterAngle, if_pos hfamily] using (hfirst ⟨hupper.1, hfamily⟩).2
    · have hL : Real.pi / 2 < z.1 := lt_of_le_of_ne (le_of_not_gt hfamily) htop.symm
      simpa only [sourceQuarterAngle, if_neg hfamily] using (hsecond ⟨hL, hupper.2⟩).2
  have hang : sourceQuarterAngle z.1 = t := by
    apply hunique t ht _ (Ioo_subset_Icc_self hquarter)
    simpa only [hxt] using hcontact
  have htq : t ∈ Ioo (0 : ℝ) (Real.pi / 2) := by simpa only [hang] using hquarter
  have hmt : Real.arctan m < t := by simpa only [hang] using hafter
  have hmatch := (fullTiltedSupportQuarterPair_other_points_after_affine
    hU hm.le haffine hρ hρ0 hρK heq ⟨htq.1.le, htq.2⟩ hmt.le).2
  have hs : Real.sin t ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi htq.1
    (by linarith only [htq.2, Real.pi_pos])).ne'
  have hc : Real.cos t ≠ 0 := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [htq.1, Real.pi_pos], htq.2⟩).ne'
  have htie : firstWall target t z.2 = secondWall target t z.2 := by
    rw [← hxt]
    change firstWall target t (Z t).1 = secondWall target t (Z t).1
    rw [hmatch, firstWall_attachedCorner target hs, secondWall_attachedCorner target hc]
  by_cases hfamily : z.1 < Real.pi / 2
  · have hθ : z.1 = t := by simpa only [sourceQuarterAngle, if_pos hfamily] using hang
    exact Or.inl ⟨⟨hupper.1, hfamily⟩, by simpa only [hθ] using htie⟩
  · have hL : Real.pi / 2 < z.1 := lt_of_le_of_ne (le_of_not_gt hfamily) htop.symm
    have hθ : z.1 - Real.pi / 2 = t := by
      simpa only [sourceQuarterAngle, if_neg hfamily] using hang
    exact Or.inr ⟨⟨hL, hupper.2⟩, by simpa only [hθ] using htie⟩

theorem coreSourceProjection_restrict_unique_image {T : Set ℝ}
    (himage : MeasurableSet (X '' T))
    (hunique : ∀ t ∈ T, ∀ s ∈ Icc (0 : ℝ) (Real.pi / 2),
      fullWallClip hU.isCap.toCompactCap (X t) s = sweptNiche target (Real.pi / 2) (X t) → s = t) :
    J.coreSourceProjection.restrict (X '' T) =
      (J.horizontalProjection : Measure ℝ).restrict (X '' T) :=
  J.coreSourceProjection_restrict_eq_of_source_support hU.isCap himage
    (J.ae_sources_over_unique_core_image hU hl hr hC hm hheight haffine hlow hhigh hh
      hρ hρ0 hρK heq hunit hunique)

theorem horizontalProjection_restrict_firstUnitPositiveInterval_eq_volume :
    (J.horizontalProjection : Measure ℝ).restrict (firstUnitPositiveInterval target C) =
      volume.restrict (firstUnitPositiveInterval target C) := by
  have hmid : Ioo (horizontalLeft target + capWidth target / 4)
      (horizontalRight target - capWidth target / 4) = Ioo (-C) C := by
    unfold capWidth
    rw [hl, hr]
    congr 1 <;> ring
  have hsub : firstUnitPositiveInterval target C ⊆ Ioo (-C) C := fun _ hx =>
    ⟨(le_max_left _ _).trans_lt hx.1, hx.2⟩
  have hbox : firstUnitPositiveInterval target C ⊆ Icc a b := by
    intro x hx
    have hla : a < -2 * C := by simpa only [hl] using hleft
    have hrb : 2 * C < b := by simpa only [hr] using hright
    have hx' := hsub hx
    constructor <;> linarith only [hla, hrb, hx'.1, hx'.2, hC]
  have hpos : ∀ x ∈ firstUnitPositiveInterval target C,
      0 < sweptNiche target (Real.pi / 2) x := by
    intro x hx
    exact (fullTiltedSupportQuarterPair_positive_middle_iff hU hm.le haffine
      hρ hρ0 hρK heq hl hr hC hm hheight hlow hhigh hh hunit (hsub hx)).mpr
        ((le_max_right _ _).trans_lt hx.1)
  exact J.horizontalProjection_restrict_Ioo_eq_volume_of_positive hU.isCap hbox
    (by rw [hmid]; exact hsub) hpos

theorem coreSourceProjection_restrict_unique_positive_image_eq_volume {T : Set ℝ}
    (himage : MeasurableSet (X '' T))
    (hpositive : ∀ t ∈ T, X t ∈ Ioo (-C) C ∧ 0 < sweptNiche target (Real.pi / 2) (X t))
    (hunique : ∀ t ∈ T, ∀ s ∈ Icc (0 : ℝ) (Real.pi / 2),
      fullWallClip hU.isCap.toCompactCap (X t) s = sweptNiche target (Real.pi / 2) (X t) → s = t) :
    J.coreSourceProjection.restrict (X '' T) = volume.restrict (X '' T) := by
  rw [J.coreSourceProjection_restrict_unique_image hU hl hr hC hm hheight haffine
    hlow hhigh hh hρ hρ0 hρK heq hunit himage hunique]
  have hpositiveSet := fullTiltedSupportQuarterPair_positive_middle_eq hU hm.le haffine
    hρ hρ0 hρK heq hl hr hC hm hheight hlow hhigh hh hunit
  have hsub : X '' T ⊆ firstUnitPositiveInterval target C := by
    rintro x ⟨t, ht, rfl⟩
    change X t ∈ Ioo (max (-C) (companionZero (leftCompanionCap target (-C)))) C
    rw [← hpositiveSet]
    exact hpositive t ht
  have hhoriz := J.horizontalProjection_restrict_firstUnitPositiveInterval_eq_volume
    hU hl hr hC hm hheight haffine hlow hhigh hh hρ hρ0 hρK heq hunit hleft hright
  have hrestrict := congrArg (fun μ : Measure ℝ => μ.restrict (X '' T)) hhoriz
  simpa only [Measure.restrict_restrict_of_subset hsub] using hrestrict

end ActualCore
end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
