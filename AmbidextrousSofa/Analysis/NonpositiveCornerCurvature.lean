module

public import AmbidextrousSofa.Analysis.FloorContactCurvature
public import Mathlib.MeasureTheory.Group.Measure

@[expose] public section

/-!
# The actual density on nonpositive corners

The negative-corner curvature-nullity theorem is transferred to any
measurable nonnegative density representing the actual curvature. The
quarter-turn translation then gives simultaneous control of both source
densities. Combining this with the proved floor-contact calculation
shows that every curvature excess above one occurs at a positive corner.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem measurable_sourceQuarterAngle : Measurable sourceQuarterAngle :=
  Measurable.ite measurableSet_Iio measurable_id (measurable_id.sub_const (Real.pi / 2))

theorem measurable_sourceCornerHeight {U : Set Plane} (hU : IsCompact U) :
    Measurable (sourceCornerHeight U) :=
  ((continuous_attachedCorner hU).measurable.comp measurable_sourceQuarterAngle).snd

/-- A null set for the actual measure has zero density almost everywhere
within that set. The density is identified by the literal restricted
measure equality, not by an arclength interpretation. -/
theorem ae_density_eq_zero_of_restrict_withDensity_null
    {μ : Measure ℝ} {S N : Set ℝ} {ρ : ℝ → ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t)
    (heq : μ.restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hN : MeasurableSet N) (hNS : N ⊆ S) (hzero : μ N = 0) :
    ∀ᵐ t ∂volume.restrict N, ρ t = 0 := by
  have hzero' : (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)) N = 0 := by
    rw [← heq, Measure.restrict_apply hN, inter_eq_left.mpr hNS, hzero]
  rw [withDensity_apply _ hN, Measure.restrict_restrict hN,
    inter_eq_left.mpr hNS] at hzero'
  have hAe : (fun t => ENNReal.ofReal (ρ t)) =ᵐ[volume.restrict N] 0 :=
    (lintegral_eq_zero_iff hρ.ennreal_ofReal).mp hzero'
  filter_upwards [hAe] with t ht
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp ht) (hρ0 t)

theorem IsFullCapMaximizer.ae_density_zero_on_negative_corners
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    {m c : ℝ} {ρ : ℝ → ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t))) :
    ∀ᵐ t : ℝ ∂volume, t ∈ regularCurvatureDomain m →
      sourceCornerHeight U t < 0 → ρ t = 0 := by
  let N : Set ℝ := {t ∈ regularCurvatureDomain m | sourceCornerHeight U t < 0}
  have hN : MeasurableSet N := (measurableSet_regularCurvatureDomain m).inter
    (measurableSet_lt (measurable_sourceCornerHeight hU.isCap.isCompact) measurable_const)
  have hzero : upperCurvature U N = 0 :=
    hU.upperCurvature_negative_corners_eq_zero hheight haffine
  have hAe := ae_density_eq_zero_of_restrict_withDensity_null hρ hρ0 heq hN
    (fun _ ht => ht.1) hzero
  have hAe' := (ae_restrict_iff' hN).mp hAe
  filter_upwards [hAe'] with t ht hregular hnegative
  exact ht ⟨hregular, hnegative⟩

/-- Both normals of the same negative corner carry zero density. The
shifted statement follows from the actual translation-invariance of
Lebesgue measure, so its null exceptional set is transported correctly. -/
theorem IsFullCapMaximizer.ae_both_densities_zero_at_negative_corner
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    {m c : ℝ} {ρ : ℝ → ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t))) :
    ∀ᵐ t ∂volume.restrict (regularCornerDomain m), (attachedCorner U t).2 < 0 →
      ρ t = 0 ∧ ρ (t + Real.pi / 2) = 0 := by
  have hAe := hU.ae_density_zero_on_negative_corners hheight haffine hρ hρ0 heq
  have hshift := (measurePreserving_add_right volume (Real.pi / 2)).quasiMeasurePreserving.ae hAe
  filter_upwards [ae_restrict_mem (isOpen_regularCornerDomain m).measurableSet,
    ae_restrict_of_ae hAe, ae_restrict_of_ae hshift] with t ht hfirst hsecond
  intro hnegative
  have hleft : sourceCornerHeight U t < 0 := by
    simpa only [sourceCornerHeight, sourceQuarterAngle, if_pos ht.1.2] using hnegative
  have hnot : ¬ t + Real.pi / 2 < Real.pi / 2 := by linarith [ht.1.1]
  have hright : sourceCornerHeight U (t + Real.pi / 2) < 0 := by
    simpa only [sourceCornerHeight, sourceQuarterAngle, if_neg hnot, add_sub_cancel_right] using
      hnegative
  exact ⟨hfirst ht.2.1 hleft, hsecond ht.2.2 hright⟩

/-- The actual maximizer has one density representation satisfying the
negative-corner zero law, floor-contact strict unit bound, and therefore
strict unit bounds everywhere at nonpositive corner height, almost
everywhere in the regular quarter-turn domain. -/
theorem IsFullCapMaximizer.curvature_density_nonpositive_corner_control
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    {m c : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ sourceKappa (upperCornerVelocity U t)) ∧
      (∀ t, ρ t ≤ 4 * (|horizontalLeft U| + |horizontalRight U| + 1) + 10) ∧
      (upperCurvature U).restrict (regularCurvatureDomain m) =
        (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)) ∧
      (∀ᵐ t ∂volume.restrict (regularCornerDomain m),
        ((attachedCorner U t).2 < 0 → ρ t = 0 ∧ ρ (t + Real.pi / 2) = 0) ∧
        ((attachedCorner U t).2 = 0 →
          0 < cornerVelocityX U t ∧ ρ t < 1 ∧ ρ (t + Real.pi / 2) < 1) ∧
        ((attachedCorner U t).2 ≤ 0 → ρ t < 1 ∧ ρ (t + Real.pi / 2) < 1)) := by
  obtain ⟨ρ, hρ, hbounds, hbound, heq, hfloor⟩ := hU.curvature_density_floor_control haffine
  have hnegative := hU.ae_both_densities_zero_at_negative_corner hheight haffine hρ
    (fun t => (hbounds t).1) heq
  refine ⟨ρ, hρ, hbounds, hbound, heq, ?_⟩
  filter_upwards [hnegative, hfloor] with t hneg hfloor
  refine ⟨hneg, hfloor, ?_⟩
  intro ht
  rcases lt_or_eq_of_le ht with ht | ht
  · have h := hneg ht
    rw [h.1, h.2]
    exact ⟨by norm_num, by norm_num⟩
  · exact (hfloor ht).2

end AmbidextrousSofa
