import AmbidextrousSofa.Analysis.JointSourcePositive
import AmbidextrousSofa.Analysis.JointSourceDensity
import AmbidextrousSofa.Analysis.TiltedSupportControls

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
  have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith only [ht.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
  have hsupport : support U (companionNormal t) = -b * Real.sin t + Real.cos t := by
    simpa only [angleSupport, ← companionNormal_eq_unitNormal] using
      hU.companionSupport_eq_high_of_affine ha hb hab haffine hhigh hs.le hc.le
        (tilted_initial_coefficient_nonneg ht.1.le htm)
  rw [secondWall, hsupport]
  apply div_neg_of_neg_of_pos _ hc
  have hgap := mul_neg_of_neg_of_pos (sub_neg.mpr hxb) hs
  nlinarith only [hgap, Real.cos_le_one t]

namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

theorem ae_sourceQuarterAngle_mem :
    ∀ᵐ z ∂(J.measure : Measure Plane),
      sourceQuarterAngle z.1 ∈ Ioo (0 : ℝ) (Real.pi / 2) := by
  filter_upwards [J.ae_angle_mem_upper, J.ae_angle_ne (Real.pi / 2)] with z hz htop
  by_cases hfirst : z.1 < Real.pi / 2
  · simpa only [sourceQuarterAngle, if_pos hfirst] using And.intro hz.1 hfirst
  · have hsecond : Real.pi / 2 < z.1 := lt_of_le_of_ne (le_of_not_gt hfirst) htop.symm
    rw [sourceQuarterAngle, if_neg hfirst]
    constructor <;> linarith only [hsecond, hz.2]

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

theorem ae_sourceQuarterAngle_gt_affine :
    ∀ᵐ z ∂(J.measure : Measure Plane), Real.arctan m < sourceQuarterAngle z.1 := by
  have hmid : middleHalfInterval (horizontalLeft target) (horizontalRight target) =
      Icc (-C) C := by
    rw [middleHalfInterval, hl, hr]
    congr 1 <;> ring
  have haff := haffine
  rw [hmid] at haff
  have hproj : AmbidextrousSofa.horizontalProjection target = Icc (-2 * C) (2 * C) := by
    rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex,
      hl, hr]
  have ha : -C ∈ AmbidextrousSofa.horizontalProjection target := by
    rw [hproj]; constructor <;> linarith only [hC]
  have hb : C ∈ AmbidextrousSofa.horizontalProjection target := by
    rw [hproj]; constructor <;> linarith only [hC]
  have hJR : horizontalRight target - capWidth target / 4 = C := by
    unfold capWidth; rw [hl, hr]; ring
  filter_upwards [J.ae_sourceQuarterAngle_mem, J.ae_angle_mem_upper,
    J.ae_angle_ne (Real.pi / 2), J.ae_spatial_mem_open_middle hU.isCap,
    J.ae_niche_pos_of_first_unit hU hl hr hC hm hheight haffine hlow hhigh hh
      hρ hρ0 hρK heq hunit,
    J.ae_first_wall_contact hU.isCap, J.ae_second_wall_contact hU.isCap]
    with z hquarter hupper htop hx hpositive hfirst hsecond
  by_contra hnot
  have hnegative := hU.isCap.secondWall_neg_before_affine_of_high_roof ha hb
    (show -C < C by linarith only [hC]) haff hhigh
    (by simpa only [hJR] using hx.2) hquarter (le_of_not_gt hnot)
  have hcontact : fullWallClip hU.isCap.toCompactCap z.2 (sourceQuarterAngle z.1) =
      sweptNiche target (Real.pi / 2) z.2 := by
    by_cases hfamily : z.1 < Real.pi / 2
    · simpa only [sourceQuarterAngle, if_pos hfamily] using
        (hfirst ⟨hupper.1, hfamily⟩).2
    · have hL : Real.pi / 2 < z.1 :=
        lt_of_le_of_ne (le_of_not_gt hfamily) htop.symm
      simpa only [sourceQuarterAngle, if_neg hfamily] using
        (hsecond ⟨hL, hupper.2⟩).2
  have hclip : fullWallClip hU.isCap.toCompactCap z.2 (sourceQuarterAngle z.1) = 0 := by
    change max (min (firstWall target (sourceQuarterAngle z.1) z.2)
      (secondWall target (sourceQuarterAngle z.1) z.2)) 0 = 0
    exact max_eq_right ((min_le_right _ _).trans hnegative.le)
  rw [hclip] at hcontact
  exact hpositive.ne hcontact

variable (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
  (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)

theorem angularMeasure_initial_companion_eq_zero :
    J.angularMeasure (Ioc (Real.pi / 2) (affineNormalAngle m)) = 0 := by
  rw [angularMeasure, Measure.map_apply measurable_fst measurableSet_Ioc]
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [J.ae_sourceQuarterAngle_gt_affine hU hl hr hC hm hheight
    haffine hlow hhigh hh hρ hρ0 hρK heq hunit] with z hz
  intro hmem
  change z.1 ∈ Ioc (Real.pi / 2) (affineNormalAngle m) at hmem
  rw [sourceQuarterAngle, if_neg (not_lt_of_ge hmem.1.le)] at hz
  unfold affineNormalAngle at hmem
  linarith only [hz, hmem.2]

theorem ae_original_companion_density_eq_cut :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      ρ (t + Real.pi / 2) = leftCompanionWingDensity m ρ (t + Real.pi / 2) := by
  have hzero := J.angularMeasure_initial_companion_eq_zero hU hl hr hC hm hheight
    haffine hlow hhigh hh hρ hρ0 hρK heq hunit
  rw [J.angularMeasure_eq_density hU hheight haffine hTargetBox hleft hright heq,
    withDensity_apply _ measurableSet_Ioc] at hzero
  have hsub : Ioc (Real.pi / 2) (affineNormalAngle m) ⊆ Ioo (0 : ℝ) Real.pi :=
    fun t ht => ⟨by linarith only [ht.1, Real.pi_pos],
      ht.2.trans_lt (affineNormalAngle_mem m).2⟩
  rw [Measure.restrict_restrict_of_subset hsub,
    lintegral_eq_zero_iff hρ.ennreal_ofReal] at hzero
  have hreal : ∀ᵐ t ∂volume.restrict (Ioc (Real.pi / 2) (affineNormalAngle m)), ρ t = 0 := by
    filter_upwards [hzero] with t ht
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp ht) (hρ0 t)
  have hglobal := (ae_restrict_iff' measurableSet_Ioc).mp hreal
  have hshift := (measurePreserving_add_right volume (Real.pi / 2)).quasiMeasurePreserving.ae
    hglobal
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hshift] with t ht hz
  by_cases hpost : Real.arctan m < t
  · exact (leftCompanionWingDensity_shift_eq_after ht.1 hpost).symm
  · have hθ : t + Real.pi / 2 ≤ affineNormalAngle m := by
      unfold affineNormalAngle
      linarith only [le_of_not_gt hpost]
    rw [leftCompanionWingDensity_eq_zero (hθ.trans (le_max_right _ _))]
    exact hz ⟨by linarith only [ht.1], hθ⟩

end ActualPair
end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
