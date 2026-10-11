module

public import AmbidextrousSofa.Analysis.JointCoreProjection

@[expose] public section

/-!
# Exact core projection at uniquely exposed corner points

Above the image of any set of uniquely exposed core contacts, every
actual source tag belongs to one of the two corner restrictions. The
core projection, their common sine-weighted horizontal projection,
therefore equals the full horizontal projection on that image, which is
Lebesgue measure inside the positive niche.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa
namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b C h m c K : ℝ} {ρ : ℝ → ℝ}
  (J : SelectedJointSourceLimit target a b)

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

variable (H : IsTiltedFirstUnitTarget target a b C h m c ρ K)

set_option quotPrecheck false
local notation "F" => fullTiltedSupportQuarterPair H.hU H.hm.le H.haffine H.hρ H.hρ0 H.hρK H.heq
local notation "Z" => innerCornerPoint (F).f (F).g
local notation "X" => (fun t => (Z t).1)

theorem ae_sources_over_unique_core_image {T : Set ℝ}
    (hunique : ∀ t ∈ T, ∀ s ∈ Icc (0 : ℝ) (Real.pi / 2),
      fullWallClip H.hU.isCap.toCompactCap (X t) s =
        sweptNiche target (Real.pi / 2) (X t) → s = t) :
    ∀ᵐ z ∂(J.measure : Measure Plane), z.2 ∈ X '' T →
      z ∈ firstCornerSource target ∪ secondCornerSource target := by
  filter_upwards [J.ae_sourceQuarterAngle_mem, J.ae_angle_mem_upper,
    J.ae_angle_ne (Real.pi / 2), J.ae_sourceQuarterAngle_gt_affine H,
    J.ae_first_wall_contact H.hU.isCap, J.ae_second_wall_contact H.hU.isCap]
    with z hquarter hupper htop hafter hfirst hsecond
  rintro ⟨t, ht, hxt⟩
  -- In either family the source angle is a contact angle of `X t`, hence equals `t`, and the
  -- two walls meet at the attached corner `Z t`.
  have htie {s : ℝ} (hs : sourceQuarterAngle z.1 = s)
      (hcontact : fullWallClip H.hU.isCap.toCompactCap z.2 s =
        sweptNiche target (Real.pi / 2) z.2) :
      firstWall target s z.2 = secondWall target s z.2 := by
    subst hs
    obtain rfl := hunique t ht _ (Ioo_subset_Icc_self hquarter) (hxt ▸ hcontact)
    rw [← hxt]
    change firstWall target _ (Z _).1 = secondWall target _ (Z _).1
    rw [(fullTiltedSupportQuarterPair_other_points_after_affine H.hU H.hm.le H.haffine H.hρ H.hρ0
        H.hρK H.heq ⟨hquarter.1.le, hquarter.2⟩ hafter.le).2,
      firstWall_attachedCorner target (sin_cos_pos_of_mem_quarter hquarter).1.ne',
      secondWall_attachedCorner target (sin_cos_pos_of_mem_quarter hquarter).2.ne']
  rcases htop.lt_or_gt with hfamily | hfamily
  · exact Or.inl ⟨⟨hupper.1, hfamily⟩, htie (ite_eq_left hfamily) (hfirst ⟨hupper.1, hfamily⟩).2⟩
  · exact Or.inr ⟨⟨hfamily, hupper.2⟩,
      htie (ite_eq_right hfamily.not_gt) (hsecond ⟨hfamily, hupper.2⟩).2⟩

include H in
theorem horizontalProjection_restrict_firstUnitPositiveInterval_eq_volume :
    (J.horizontalProjection : Measure ℝ).restrict (firstUnitPositiveInterval target C) =
      volume.restrict (firstUnitPositiveInterval target C) := by
  have hsub : firstUnitPositiveInterval target C ⊆ Ioo (-C) C := fun _ hx =>
    (H.positive_middle_eq.ge hx).1
  exact J.horizontalProjection_restrict_Ioo_eq_volume_of_positive H.hU.isCap
    (hsub.trans H.Ioo_subset_box) (hsub.trans H.middle_eq.ge) fun x hx =>
      (H.positive_middle_eq.ge hx).2

theorem coreSourceProjection_restrict_unique_positive_image_eq_volume {T : Set ℝ}
    (himage : MeasurableSet (X '' T))
    (hpositive : ∀ t ∈ T, X t ∈ Ioo (-C) C ∧ 0 < sweptNiche target (Real.pi / 2) (X t))
    (hunique : ∀ t ∈ T, ∀ s ∈ Icc (0 : ℝ) (Real.pi / 2),
      fullWallClip H.hU.isCap.toCompactCap (X t) s =
        sweptNiche target (Real.pi / 2) (X t) → s = t) :
    J.coreSourceProjection.restrict (X '' T) = volume.restrict (X '' T) := by
  have hsub : X '' T ⊆ firstUnitPositiveInterval target C := by
    rintro x ⟨t, ht, rfl⟩
    exact H.positive_middle_eq.le (hpositive t ht)
  rw [J.coreSourceProjection_restrict_eq_of_source_support himage
      (J.ae_sources_over_unique_core_image H hunique),
    ← Measure.restrict_restrict_of_subset (μ := (J.horizontalProjection : Measure ℝ)) hsub,
    J.horizontalProjection_restrict_firstUnitPositiveInterval_eq_volume H,
    Measure.restrict_restrict_of_subset hsub]

end ActualCore
end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
