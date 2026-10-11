module

public import AmbidextrousSofa.Analysis.JointSourcePositive
public import AmbidextrousSofa.Analysis.JointSourceDensity
public import AmbidextrousSofa.Analysis.TiltedSupportControls

@[expose] public section

/-!
# The actual source support lies after the affine normal

Before the positive affine normal, the original companion wall is
supported by the high middle point and lies strictly below the floor at
every interior middle abscissa. A positive niche contact is impossible
there, for either source family. The resulting zero angular interval
also identifies the original companion density with the cut-wing
density almost everywhere, including the part removed by the cut.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem IsDownwardCap.secondWall_neg_before_affine_of_high_roof
    {U : Set Plane} (hU : IsDownwardCap U) {a b m c x t : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (haffine : ∀ y ∈ Icc a b, capRoof U y = m * y + c)
    (hhigh : capRoof U b = 1) (hxb : x < b)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) (htm : t ≤ Real.arctan m) :
    secondWall U t x < 0 := by
  have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  have hsupport : support U (companionNormal t) = -b * Real.sin t + Real.cos t := by
    simpa only [angleSupport, ← companionNormal_eq_unitNormal] using
      hU.companionSupport_eq_high_of_affine ha hb hab haffine hhigh hs.le hc.le
        (tilted_initial_coefficient_nonneg ht.1.le htm)
  rw [secondWall, hsupport]
  exact div_neg_of_neg_of_pos (by nlinarith [Real.cos_le_one t]) hc

namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

theorem ae_sourceQuarterAngle_mem :
    ∀ᵐ z ∂(J.measure : Measure Plane),
      sourceQuarterAngle z.1 ∈ Ioo (0 : ℝ) (Real.pi / 2) := by
  filter_upwards [J.ae_angle_mem_upper, J.ae_angle_ne (Real.pi / 2)] with z hz htop
  rcases htop.lt_or_gt with h | h
  · rw [sourceQuarterAngle, ite_eq_left h]
    exact ⟨hz.1, h⟩
  · rw [sourceQuarterAngle, ite_eq_right h.not_gt]
    constructor <;> linarith [hz.2]

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

include hU C hl hr hC hm hheight haffine hlow hhigh hh hρ hρ0 hρK heq hunit in
theorem ae_sourceQuarterAngle_gt_affine :
    ∀ᵐ z ∂(J.measure : Measure Plane), Real.arctan m < sourceQuarterAngle z.1 := by
  have hmid : middleHalfInterval (horizontalLeft target) (horizontalRight target) =
      Icc (-C) C := by
    rw [middleHalfInterval, hl, hr]
    congr 1 <;> ring
  have hproj : AmbidextrousSofa.horizontalProjection target = Icc (-2 * C) (2 * C) := by
    rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex,
      hl, hr]
  have hJR : horizontalRight target - capWidth target / 4 = C := by
    unfold capWidth; rw [hl, hr]; ring
  filter_upwards [J.ae_sourceQuarterAngle_mem, J.ae_angle_mem_upper,
    J.ae_angle_ne (Real.pi / 2), J.ae_spatial_mem_open_middle hU.isCap,
    J.ae_niche_pos_of_first_unit hU hl hr hC hm hheight haffine hlow hhigh hh
      hρ hρ0 hρK heq hunit,
    J.ae_first_wall_contact hU.isCap, J.ae_second_wall_contact hU.isCap]
    with z hquarter hupper htop hx hpositive hfirst hsecond
  by_contra hnot
  have hneg := hU.isCap.secondWall_neg_before_affine_of_high_roof
    (by rw [hproj]; constructor <;> linarith) (by rw [hproj]; constructor <;> linarith)
    (by linarith) (hmid ▸ haffine) hhigh (hJR ▸ hx.2) hquarter (le_of_not_gt hnot)
  have hclip : fullWallClip hU.isCap.toCompactCap z.2 (sourceQuarterAngle z.1) = 0 :=
    max_eq_right ((min_le_right _ _).trans hneg.le)
  rcases htop.lt_or_gt with hz | hz
  · rw [sourceQuarterAngle, ite_eq_left hz] at hclip
    exact hpositive.ne' ((hfirst ⟨hupper.1, hz⟩).2.symm.trans hclip)
  · rw [sourceQuarterAngle, ite_eq_right hz.not_gt] at hclip
    exact hpositive.ne' ((hsecond ⟨hz, hupper.2⟩).2.symm.trans hclip)

variable (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
  (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)

include J hU hl hr hC hm hheight haffine hlow hhigh hh hρ hρ0 hρK heq hunit hTargetBox hleft
  hright in
theorem ae_original_companion_density_eq_cut :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      ρ (t + Real.pi / 2) = leftCompanionWingDensity m ρ (t + Real.pi / 2) := by
  have hzero : J.angularMeasure (Ioc (Real.pi / 2) (affineNormalAngle m)) = 0 := by
    rw [angularMeasure, Measure.map_apply measurable_fst measurableSet_Ioc,
      measure_eq_zero_iff_ae_notMem]
    filter_upwards [J.ae_sourceQuarterAngle_gt_affine hU hl hr hC hm hheight
      haffine hlow hhigh hh hρ hρ0 hρK heq hunit] with z hz hmem
    rw [sourceQuarterAngle, ite_eq_right hmem.1.not_gt] at hz
    linarith [hmem.2, show affineNormalAngle m = Real.arctan m + Real.pi / 2 from rfl]
  have hsub : Ioc (Real.pi / 2) (affineNormalAngle m) ⊆ Ioo (0 : ℝ) Real.pi :=
    fun t ht => ⟨by linarith [ht.1, Real.pi_pos], ht.2.trans_lt (affineNormalAngle_mem m).2⟩
  rw [J.angularMeasure_eq_density hU hheight haffine hTargetBox hleft hright heq,
    withDensity_apply _ measurableSet_Ioc, Measure.restrict_restrict_of_subset hsub,
    lintegral_eq_zero_iff hρ.ennreal_ofReal] at hzero
  have hshift := (measurePreserving_add_right volume (Real.pi / 2)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' measurableSet_Ioc).mp hzero)
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hshift] with t ht hz
  by_cases hpost : Real.arctan m < t
  · exact (leftCompanionWingDensity_shift_eq_after ht.1 hpost).symm
  · have hθ : t + Real.pi / 2 ≤ affineNormalAngle m := by
      unfold affineNormalAngle; linarith
    rw [leftCompanionWingDensity_eq_zero (hθ.trans (le_max_right _ _))]
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp (hz ⟨by linarith [ht.1], hθ⟩)) (hρ0 _)

end ActualPair
end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
