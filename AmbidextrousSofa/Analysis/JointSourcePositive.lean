module

public import AmbidextrousSofa.Analysis.JointSourceContactLimit
public import AmbidextrousSofa.Analysis.FirstUnitProjection
public import AmbidextrousSofa.Analysis.DrySourceProjection

@[expose] public section

/-!
# No floor-only mass in the actual common source limit

On a compact strictly dry interval the finite positive horizontal length
tends to zero. The sine projection of the same joint limit therefore
vanishes there. Exhausting the open dry interval and removing its single
zero endpoint leaves only positive niche contacts. Positivity of the
sine weight transfers this conclusion to the unweighted joint measure.
The final theorem derives its dry interval from the actual low wing and
the already proved first-unit bound; no support or occupation premise is
added to the tilted cap problem.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa
namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

theorem horizontalProjection_Ioc_eq_zero_of_dry
    (hTarget : IsDownwardCap target) {l r : ℝ} (hlr : l ≤ r)
    (hL : horizontalLeft target + capWidth target / 4 < l)
    (hR : r < horizontalRight target - capWidth target / 4)
    (hnegative : ∀ x ∈ Icc l r, ∀ t ∈ Ioc (0 : ℝ) (Real.pi / 2),
      secondWallNumerator target t x < 0) :
    (J.horizontalProjection : Measure ℝ) (Ioc l r) = 0 := by
  have hzero := finitePositiveLength_tendsto_zero_on_dry_interval
    J.hausdorff J.isCap hTarget J.level_tendsto
    (show 0 ≤ |a| + |b| + 1 by positivity)
    (fun n => subset_symmetricBox_of_horizontalBox (J.selected n).inBox)
    hlr hL hR hnegative
  have hzeroIntegral : Tendsto
      (fun n => ∫ z : Plane, Real.sin z.1
        ∂innerJointMeasure (J.caps n) (dyadic (J.level n)) l r)
      (sourceLimitFilter : Filter ℕ) (𝓝 0) := by
    simpa only [integral_innerJointMeasure_sin _ _ hlr] using
      hzero.mono_left sourceLimitFilter_le_atTop
  have hflux : (∫ z in univ ×ˢ Ioc l r, Real.sin z.1
      ∂(J.measure : Measure Plane)) = 0 :=
    tendsto_nhds_unique
      (J.local_test_integral_tendsto hTarget sourceSineFunction hL hR) hzeroIntegral
  apply (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
  rw [J.horizontalProjection_real_eq_sine_integral measurableSet_Ioc, hflux]

theorem horizontalProjection_Ioo_eq_zero_of_dry
    (hTarget : IsDownwardCap target) {l r : ℝ}
    (hmiddle : Ioo l r ⊆ Ioo (horizontalLeft target + capWidth target / 4)
      (horizontalRight target - capWidth target / 4))
    (hnegative : ∀ x ∈ Ioo l r, ∀ t ∈ Ioc (0 : ℝ) (Real.pi / 2),
      secondWallNumerator target t x < 0) :
    (J.horizontalProjection : Measure ℝ) (Ioo l r) = 0 := by
  apply Measure.restrict_eq_zero.mp
  have heq : (J.horizontalProjection : Measure ℝ).restrict (Ioo l r) =
      (0 : Measure ℝ).restrict (Ioo l r) := by
    apply measure_restrict_Ioo_eq_of_closed_subintervals
    intro x y hxy
    rw [Measure.restrict_zero]
    apply Measure.restrict_eq_zero.mpr
    by_cases hspan : x ≤ y
    · have hx := hxy (left_mem_Icc.mpr hspan)
      have hy := hxy (right_mem_Icc.mpr hspan)
      exact J.horizontalProjection_Ioc_eq_zero_of_dry hTarget hspan
        (hmiddle hx).1 (hmiddle hy).2 (fun z hz => hnegative z (hxy hz))
    · simp only [Ioc_eq_empty_of_le (le_of_not_ge hspan), measure_empty]
  simpa only [Measure.restrict_zero] using heq

theorem spatial_Ioo_eq_zero_of_dry
    (hTarget : IsDownwardCap target) {l r : ℝ}
    (hmiddle : Ioo l r ⊆ Ioo (horizontalLeft target + capWidth target / 4)
      (horizontalRight target - capWidth target / 4))
    (hnegative : ∀ x ∈ Ioo l r, ∀ t ∈ Ioc (0 : ℝ) (Real.pi / 2),
      secondWallNumerator target t x < 0) :
    (J.measure : Measure Plane) (univ ×ˢ Ioo l r) = 0 := by
  apply absolutelyContinuous_weightedFiniteMeasure J.measure sourceSineFunction.nnrealPart
    J.sinePart_ne_zero_ae
  rw [← sourceHorizontalProjection_apply _ measurableSet_Ioo]
  exact J.horizontalProjection_Ioo_eq_zero_of_dry hTarget hmiddle hnegative

/-- Every actual source abscissa is strictly inside the middle window:
the limiting endpoints are two null spatial fibers. -/
theorem ae_spatial_mem_open_middle (hTarget : IsDownwardCap target) :
    ∀ᵐ z ∂(J.measure : Measure Plane),
      z.2 ∈ Ioo (horizontalLeft target + capWidth target / 4)
        (horizontalRight target - capWidth target / 4) := by
  have hleft := measure_eq_zero_iff_ae_notMem.mp
    (J.spatial_fiber_eq_zero (horizontalLeft target + capWidth target / 4))
  have hright := measure_eq_zero_iff_ae_notMem.mp
    (J.spatial_fiber_eq_zero (horizontalRight target - capWidth target / 4))
  filter_upwards [J.ae_spatial_mem_middle hTarget, hleft, hright] with z hz hl hr
  have hzl : z.2 ≠ horizontalLeft target + capWidth target / 4 :=
    fun heq => hl ⟨mem_univ _, heq⟩
  have hzr : z.2 ≠ horizontalRight target - capWidth target / 4 :=
    fun heq => hr ⟨mem_univ _, heq⟩
  exact ⟨lt_of_le_of_ne hz.1 hzl.symm, lt_of_le_of_ne hz.2 hzr⟩

/-- The floor and the zero endpoint carry no actual joint source mass.
Only natural cap data and the proved first density bound are used. -/
theorem ae_niche_pos_of_first_unit
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
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1) :
    ∀ᵐ z ∂(J.measure : Measure Plane), 0 < sweptNiche target (Real.pi / 2) z.2 := by
  let z₀ := companionZero (leftCompanionCap target (-C))
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
  have hab : -C < C := by linarith only [hC]
  have hV := hU.isCap.leftCompanionCap ha
  have hVheight : capHeight (leftCompanionCap target (-C)) < 1 := by
    rw [(hU.isCap.top_leftCompanionCap_of_positive_affine ha hb hab hm haff).1, hlow]
    linarith only [hh]
  have hVleft : 0 < capRoof (leftCompanionCap target (-C))
      (horizontalLeft (leftCompanionCap target (-C))) := by
    rw [horizontalLeft_leftCompanionCap hU.isCap ha,
      hU.isCap.capRoof_leftCompanionCap ha ⟨le_rfl, by rw [hl]; linarith only [hC]⟩]
    exact (hU.endpoint_heights_pos_of_affine hheight ⟨m, c, haffine⟩).2
  have hzaxis : z₀ < horizontalLeft target + 1 := by
    simpa only [horizontalLeft_leftCompanionCap hU.isCap ha] using
      hV.companionZero_lt_left_add_one hVheight hVleft
  have hzC : z₀ < C := by rw [hl] at hzaxis; linarith only [hzaxis, hC]
  have hW : capWidth target = 4 * C := by unfold capWidth; rw [hl, hr]; ring
  have hJL : horizontalLeft target + capWidth target / 4 = -C := by rw [hl, hW]; ring
  have hJR : horizontalRight target - capWidth target / 4 = C := by rw [hr, hW]; ring
  have hdry := J.spatial_Ioo_eq_zero_of_dry hU.isCap
    (l := -C) (r := z₀)
    (by rw [hJL, hJR]; exact Ioo_subset_Ioo le_rfl hzC.le)
    (fun x hx t ht => hU.isCap.secondWallNumerator_neg_of_lt_low_wing_zero
      ha hb hab haff hhigh (hx.2.trans hzC) hx.2 (hx.2.trans hzaxis) ht)
  have hnotdry := measure_eq_zero_iff_ae_notMem.mp hdry
  have hnotzero := measure_eq_zero_iff_ae_notMem.mp (J.spatial_fiber_eq_zero z₀)
  have hmiddle := J.ae_spatial_mem_open_middle hU.isCap
  rw [hJL, hJR] at hmiddle
  filter_upwards [hmiddle, hnotdry, hnotzero] with z hz hn hz₀
  have hzx : z₀ ≤ z.2 := by
    by_contra hnot
    exact hn ⟨mem_univ _, hz.1, lt_of_not_ge hnot⟩
  have hne : z₀ ≠ z.2 := fun heq => hz₀ ⟨mem_univ _, heq.symm⟩
  exact (fullTiltedSupportQuarterPair_positive_middle_iff
    hU hm.le haffine hρ hρ0 hρK heq hl hr hC hm hheight hlow hhigh hh hunit hz).mpr
      (lt_of_le_of_ne hzx hne)

end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
