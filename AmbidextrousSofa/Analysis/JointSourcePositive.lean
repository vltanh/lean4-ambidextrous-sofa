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
    J.hausdorff J.isCap hTarget J.level_tendsto (show 0 ≤ |a| + |b| + 1 by positivity)
    (fun n => subset_symmetricBox_of_horizontalBox (J.selected n).inBox) hlr hL hR hnegative
  simp only [← integral_innerJointMeasure_sin _ _ hlr] at hzero
  rw [← measureReal_eq_zero_iff (measure_ne_top _ _),
    J.horizontalProjection_real_eq_sine_integral measurableSet_Ioc]
  exact tendsto_nhds_unique (J.local_test_integral_tendsto hTarget sourceSineFunction hL hR)
    (hzero.mono_left sourceLimitFilter_le_atTop)

theorem spatial_Ioo_eq_zero_of_dry
    (hTarget : IsDownwardCap target) {l r : ℝ}
    (hmiddle : Ioo l r ⊆ Ioo (horizontalLeft target + capWidth target / 4)
      (horizontalRight target - capWidth target / 4))
    (hnegative : ∀ x ∈ Ioo l r, ∀ t ∈ Ioc (0 : ℝ) (Real.pi / 2),
      secondWallNumerator target t x < 0) :
    (J.measure : Measure Plane) (univ ×ˢ Ioo l r) = 0 := by
  refine absolutelyContinuous_weightedFiniteMeasure J.measure sourceSineFunction.nnrealPart
    J.sinePart_ne_zero_ae ?_
  rw [← sourceHorizontalProjection_apply _ measurableSet_Ioo, ← Measure.restrict_eq_zero,
    ← Measure.restrict_zero (Ioo l r)]
  refine measure_restrict_Ioo_eq_of_closed_subintervals fun x y hxy => ?_
  rw [Measure.restrict_zero, Measure.restrict_eq_zero]
  rcases le_or_gt x y with hxy' | hxy'
  · exact J.horizontalProjection_Ioc_eq_zero_of_dry hTarget hxy'
      (hmiddle (hxy (left_mem_Icc.2 hxy'))).1 (hmiddle (hxy (right_mem_Icc.2 hxy'))).2
      fun z hz => hnegative z (hxy hz)
  · simp [Ioc_eq_empty_of_le hxy'.le]

/-- Every actual source abscissa is strictly inside the middle window:
the limiting endpoints are two null spatial fibers. -/
theorem ae_spatial_mem_open_middle (hTarget : IsDownwardCap target) :
    ∀ᵐ z ∂(J.measure : Measure Plane),
      z.2 ∈ Ioo (horizontalLeft target + capWidth target / 4)
        (horizontalRight target - capWidth target / 4) := by
  filter_upwards [J.ae_spatial_mem_middle hTarget, measure_eq_zero_iff_ae_notMem.mp
    (J.spatial_fiber_eq_zero (horizontalLeft target + capWidth target / 4)),
    measure_eq_zero_iff_ae_notMem.mp
      (J.spatial_fiber_eq_zero (horizontalRight target - capWidth target / 4))] with z hz hl hr
  exact ⟨hz.1.lt_of_ne fun h => hl ⟨mem_univ _, h.symm⟩, hz.2.lt_of_ne fun h => hr ⟨mem_univ _, h⟩⟩

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
  have haff : ∀ x ∈ Icc (-C) C, capRoof target x = m * x + c := fun x hx => haffine x (by
    rw [middleHalfInterval, hl, hr]; constructor <;> linarith only [hx.1, hx.2])
  obtain ⟨ha, hb⟩ : -C ∈ AmbidextrousSofa.horizontalProjection target ∧
      C ∈ AmbidextrousSofa.horizontalProjection target := by
    rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex, hl, hr]
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hab : -C < C := by linarith only [hC]
  have hzaxis := (hU.isCap.leftCompanionCap ha).companionZero_lt_left_add_one
    (by rw [(hU.isCap.top_leftCompanionCap_of_positive_affine ha hb hab hm haff).1, hlow]
        linarith only [hh])
    (by rw [horizontalLeft_leftCompanionCap hU.isCap ha,
          hU.isCap.capRoof_leftCompanionCap ha ⟨le_rfl, by rw [hl]; linarith only [hC]⟩]
        exact (hU.endpoint_heights_pos_of_affine hheight ⟨m, c, haffine⟩).2)
  rw [horizontalLeft_leftCompanionCap hU.isCap ha] at hzaxis
  have hzC : companionZero (leftCompanionCap target (-C)) < C := by linarith only [hzaxis, hl, hC]
  have hJ : Ioo (horizontalLeft target + capWidth target / 4)
      (horizontalRight target - capWidth target / 4) = Ioo (-C) C := by
    unfold capWidth; rw [hl, hr]; congr 1 <;> ring
  filter_upwards [hJ ▸ J.ae_spatial_mem_open_middle hU.isCap, measure_eq_zero_iff_ae_notMem.mp
      (J.spatial_Ioo_eq_zero_of_dry hU.isCap (l := -C) (hJ ▸ Ioo_subset_Ioo le_rfl hzC.le)
      fun x hx t ht => hU.isCap.secondWallNumerator_neg_of_lt_low_wing_zero
        ha hb hab haff hhigh (hx.2.trans hzC) hx.2 (hx.2.trans hzaxis) ht),
    measure_eq_zero_iff_ae_notMem.mp (J.spatial_fiber_eq_zero _)] with z hz hn hz₀
  exact (fullTiltedSupportQuarterPair_positive_middle_iff hU hm.le haffine hρ hρ0 hρK heq hl hr hC
    hm hheight hlow hhigh hh hunit hz).2 ((not_lt.1 fun h => hn ⟨mem_univ _, hz.1, h⟩).lt_of_ne
      fun h => hz₀ ⟨mem_univ _, h.symm⟩)

end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
