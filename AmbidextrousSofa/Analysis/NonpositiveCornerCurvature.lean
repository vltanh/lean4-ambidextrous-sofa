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

theorem measurable_sourceCornerHeight {U : Set Plane} (hU : IsCompact U) :
    Measurable (sourceCornerHeight U) :=
  ((continuous_attachedCorner hU).measurable.comp (Measurable.ite measurableSet_Iio measurable_id
    (measurable_id.sub_const (Real.pi / 2)))).snd

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
  rw [withDensity_apply _ hN, Measure.restrict_restrict hN, inter_eq_left.mpr hNS,
    lintegral_eq_zero_iff hρ.ennreal_ofReal] at hzero'
  filter_upwards [hzero'] with t ht
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp ht) (hρ0 t)

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
  refine ⟨ρ, hρ, hbounds, hbound, heq, ?_⟩
  -- The density vanishes almost everywhere on the negative corners, whose curvature is zero.
  have hN : MeasurableSet {t ∈ regularCurvatureDomain m | sourceCornerHeight U t < 0} :=
    (measurableSet_regularCurvatureDomain m).inter
      (measurableSet_lt (measurable_sourceCornerHeight hU.isCap.isCompact) measurable_const)
  have hAe : ∀ᵐ t, t ∈ regularCurvatureDomain m → sourceCornerHeight U t < 0 → ρ t = 0 := by
    filter_upwards [(ae_restrict_iff' hN).mp (ae_density_eq_zero_of_restrict_withDensity_null hρ
      (fun t => (hbounds t).1) heq hN (fun _ ht => ht.1)
      (hU.upperCurvature_negative_corners_eq_zero hheight haffine))] with t ht hregular hnegative
    exact ht ⟨hregular, hnegative⟩
  -- Translation invariance of Lebesgue measure transports the null set to the shifted normal.
  have hshift := (measurePreserving_add_right volume (Real.pi / 2)).quasiMeasurePreserving.ae hAe
  filter_upwards [ae_restrict_mem (isOpen_regularCornerDomain m).measurableSet,
    ae_restrict_of_ae hAe, ae_restrict_of_ae hshift, hfloor] with t ht hfirst hsecond hfloor
  have hneg (hnegative : (attachedCorner U t).2 < 0) : ρ t = 0 ∧ ρ (t + Real.pi / 2) = 0 :=
    ⟨hfirst ht.2.1 (by rwa [sourceCornerHeight, sourceQuarterAngle, ite_eq_left ht.1.2]),
      hsecond ht.2.2 (by rwa [sourceCornerHeight, sourceQuarterAngle,
        ite_eq_right (not_lt.mpr (by linarith [ht.1.1])), add_sub_cancel_right])⟩
  refine ⟨hneg, hfloor, fun ht => ?_⟩
  rcases ht.lt_or_eq with ht | ht
  · simp [hneg ht]
  · exact (hfloor ht).2

end AmbidextrousSofa
