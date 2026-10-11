module

public import AmbidextrousSofa.Analysis.JointCoreFlux
public import AmbidextrousSofa.Analysis.JointCoreProjection

@[expose] public section

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

theorem coreSourceProjection_restrict_eq_of_source_support {E : Set ℝ} (hE : MeasurableSet E)
    (hsource : ∀ᵐ z ∂(J.measure : Measure Plane), z.2 ∈ E →
      z ∈ firstCornerSource target ∪ secondCornerSource target) :
    J.coreSourceProjection.restrict E = (J.horizontalProjection : Measure ℝ).restrict E := by
  have hE' : MeasurableSet (Prod.snd ⁻¹' E : Set Plane) := hE.preimage measurable_snd
  rw [coreSourceProjection, ← J.source_sine_spatial_eq_horizontalProjection,
    Measure.restrict_map measurable_snd hE, Measure.restrict_map measurable_snd hE,
    restrict_withDensity hE', restrict_withDensity hE', sourceBranchMeasure,
    Measure.restrict_restrict hE']
  congr 2
  exact Measure.restrict_congr_set (hsource.mono fun z hz =>
    propext ⟨fun ht => ht.1, fun ht => ⟨ht, hz ht⟩⟩)

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
set_option quotPrecheck false in
local notation "Z" => innerCornerPoint (F).f (F).g
set_option quotPrecheck false in
local notation "p" => supportP (F).fD (F).g
set_option quotPrecheck false in
local notation "q" => supportQ (F).gD (F).f
set_option quotPrecheck false in
local notation "X" => (fun t => (Z t).1)
local notation "aZ" => J.sourceBranchDensity (firstCornerSource target) 0
local notation "aW" => J.sourceBranchDensity (secondCornerSource target) (Real.pi / 2)
local notation "w" => (fun t => aZ t * Real.sin t + aW t * Real.cos t)

include hl hr hC hheight hlow hhigh hh hunit hTargetBox hleft hright in
theorem coreSourceProjection_eq_density_graph {α η : ℝ}
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) :
    J.coreSourceProjection =
      ((volume.restrict (Ioo α η)).withDensity (fun t => ENNReal.ofReal (w t))).map X := by
  have hX := (fullTiltedSupportQuarterPair_core_continuous_global
    hU hm.le haffine hρ hρ0 hρK heq).1.measurable
  -- Along the corner graph, the weighted horizontal projection of each branch is the
  -- push-forward of its weighted angular density.
  have hgraph {S : Set Plane} {d : ℝ} (hS : ∀ᵐ z ∂J.sourceBranchMeasure S, z.2 = X (z.1 - d)) :
      ((J.sourceBranchMeasure S).withDensity fun z =>
        ENNReal.ofReal (Real.sin z.1)).map Prod.snd = (volume.withDensity fun t =>
          ENNReal.ofReal (J.sourceBranchDensity S d t * Real.sin (t + d))).map X := by
    rw [← J.sourceBranch_density_sine_eq hU hheight haffine hTargetBox hleft hright heq]
    simpa only [sourceBranchAngular, sub_add_cancel] using graph_weighted_map_eq
      (W := fun t => ENNReal.ofReal (Real.sin (t + d))) (measurable_fst.sub_const d) hX
      (Real.measurable_sin.comp (measurable_id.add_const d)).ennreal_ofReal hS
  have hw : Measurable fun t => ENNReal.ofReal (aZ t * Real.sin (t + 0)) :=
    ((J.measurable_sourceBranchDensity _ _).mul
      (Real.measurable_sin.comp (measurable_id.add_const 0))).ennreal_ofReal
  have hz := J.ae_corner_density_zero_off_core hU hl hr hC hm hheight haffine
    hlow hhigh hh hρ hρ0 hρK heq hunit hTargetBox hleft hright hphase
  -- Both densities vanish off the core, where both weights are nonnegative.
  have hdens : (volume.restrict (Ioo α η)).withDensity (fun t => ENNReal.ofReal (w t)) =
      volume.withDensity (fun t => ENNReal.ofReal (aZ t * Real.sin (t + 0))) +
        volume.withDensity (fun t => ENNReal.ofReal (aW t * Real.sin (t + Real.pi / 2))) := by
    rw [← withDensity_indicator measurableSet_Ioo, ← withDensity_add_left hw]
    refine withDensity_congr_ae ?_
    filter_upwards [hz] with t ht
    by_cases hc : t ∈ Ioo α η
    · have htq : t ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨hphase.first_mem.1.trans hc.1, hc.2.trans hphase.second_mem.2⟩
      simp only [indicator_of_mem hc, Pi.add_apply, add_zero, Real.sin_add_pi_div_two]
      exact ENNReal.ofReal_add (mul_nonneg (J.sourceBranchDensity_nonneg _ _ _)
        (Real.sin_pos_of_pos_of_lt_pi htq.1 (by linarith only [htq.2, Real.pi_pos])).le)
        (mul_nonneg (J.sourceBranchDensity_nonneg _ _ _)
          (Real.cos_pos_of_mem_Ioo ⟨by linarith only [htq.1, Real.pi_pos], htq.2⟩).le)
    · simp [indicator_of_notMem hc, (ht hc).1, (ht hc).2]
  have hunion : J.sourceBranchMeasure (firstCornerSource target ∪ secondCornerSource target) =
      J.sourceBranchMeasure (firstCornerSource target) +
        J.sourceBranchMeasure (secondCornerSource target) :=
    Measure.restrict_union (disjoint_sourceSlices.mono inter_subset_left inter_subset_left)
      (measurableSet_secondCornerSource hU.isCap.isCompact)
  rw [coreSourceProjection, hunion, withDensity_add_measure, Measure.map_add _ _ measurable_snd,
    hgraph (d := 0) ((J.ae_first_corner_core_geometry hU hl hr hC hm hheight haffine hlow hhigh
      hh hρ hρ0 hρK heq hunit hleft hright hphase).mono fun z hz => by
        simpa only [sub_zero] using hz.2.1),
    hgraph ((J.ae_second_corner_core_geometry hU hl hr hC hm hheight haffine hlow hhigh hh
      hρ hρ0 hρK heq hunit hleft hright hphase).mono fun z hz => hz.2.1),
    ← Measure.map_add _ _ hX, hdens]

include hl hr hC hheight hlow hhigh hh hunit in
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
  -- In either family the source angle is a contact angle of `X t`, hence equals `t`, and the
  -- two walls meet at the attached corner `Z t`.
  have htie {s : ℝ} (hs : sourceQuarterAngle z.1 = s)
      (hcontact : fullWallClip hU.isCap.toCompactCap z.2 s = sweptNiche target (Real.pi / 2) z.2) :
      firstWall target s z.2 = secondWall target s z.2 := by
    subst hs
    obtain rfl := hunique t ht _ (Ioo_subset_Icc_self hquarter) (hxt ▸ hcontact)
    rw [← hxt]
    change firstWall target _ (Z _).1 = secondWall target _ (Z _).1
    rw [(fullTiltedSupportQuarterPair_other_points_after_affine hU hm.le haffine hρ hρ0 hρK heq
        ⟨hquarter.1.le, hquarter.2⟩ hafter.le).2,
      firstWall_attachedCorner target (Real.sin_pos_of_pos_of_lt_pi hquarter.1
        (by linarith only [hquarter.2, Real.pi_pos])).ne',
      secondWall_attachedCorner target (Real.cos_pos_of_mem_Ioo
        ⟨by linarith only [hquarter.1, Real.pi_pos], hquarter.2⟩).ne']
  rcases htop.lt_or_gt with hfamily | hfamily
  · exact Or.inl ⟨⟨hupper.1, hfamily⟩, htie (ite_eq_left hfamily) (hfirst ⟨hupper.1, hfamily⟩).2⟩
  · exact Or.inr ⟨⟨hfamily, hupper.2⟩,
      htie (ite_eq_right hfamily.not_gt) (hsecond ⟨hfamily, hupper.2⟩).2⟩

include hU hl hr hC hm hheight haffine hlow hhigh hh hρ hρ0 hρK heq hunit hleft hright in
theorem horizontalProjection_restrict_firstUnitPositiveInterval_eq_volume :
    (J.horizontalProjection : Measure ℝ).restrict (firstUnitPositiveInterval target C) =
      volume.restrict (firstUnitPositiveInterval target C) := by
  have hsub : firstUnitPositiveInterval target C ⊆ Ioo (-C) C := fun _ hx =>
    ⟨(le_max_left _ _).trans_lt hx.1, hx.2⟩
  refine J.horizontalProjection_restrict_Ioo_eq_volume_of_positive hU.isCap
    (fun x hx => ⟨by linarith [(hsub hx).1], by linarith [(hsub hx).2]⟩)
    (fun x hx => by rw [capWidth, hl, hr]; constructor <;> linarith [(hsub hx).1, (hsub hx).2])
    fun x hx => (fullTiltedSupportQuarterPair_positive_middle_iff hU hm.le haffine
      hρ hρ0 hρK heq hl hr hC hm hheight hlow hhigh hh hunit (hsub hx)).mpr
        ((le_max_right _ _).trans_lt hx.1)

include hl hr hC hheight hlow hhigh hh hunit hleft hright in
theorem coreSourceProjection_restrict_unique_positive_image_eq_volume {T : Set ℝ}
    (himage : MeasurableSet (X '' T))
    (hpositive : ∀ t ∈ T, X t ∈ Ioo (-C) C ∧ 0 < sweptNiche target (Real.pi / 2) (X t))
    (hunique : ∀ t ∈ T, ∀ s ∈ Icc (0 : ℝ) (Real.pi / 2),
      fullWallClip hU.isCap.toCompactCap (X t) s = sweptNiche target (Real.pi / 2) (X t) → s = t) :
    J.coreSourceProjection.restrict (X '' T) = volume.restrict (X '' T) := by
  have hsub : X '' T ⊆ firstUnitPositiveInterval target C := by
    rintro x ⟨t, ht, rfl⟩
    rw [firstUnitPositiveInterval, ← fullTiltedSupportQuarterPair_positive_middle_eq hU hm.le
      haffine hρ hρ0 hρK heq hl hr hC hm hheight hlow hhigh hh hunit]
    exact hpositive t ht
  rw [J.coreSourceProjection_restrict_eq_of_source_support himage
      (J.ae_sources_over_unique_core_image hU hl hr hC hm hheight haffine hlow hhigh hh
        hρ hρ0 hρK heq hunit hunique),
    ← Measure.restrict_restrict_of_subset (μ := (J.horizontalProjection : Measure ℝ)) hsub,
    J.horizontalProjection_restrict_firstUnitPositiveInterval_eq_volume hU hl hr hC hm hheight
      haffine hlow hhigh hh hρ hρ0 hρK heq hunit hleft hright,
    Measure.restrict_restrict_of_subset hsub]

end ActualCore
end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
