module

public import AmbidextrousSofa.Analysis.JointSourceDensity
public import AmbidextrousSofa.Analysis.FirstUnitProjection
public import AmbidextrousSofa.Analysis.DrySourceProjection

@[expose] public section

/-!
# No floor-only mass in the actual common source limit

In the middle window of the tilted target, the niche is positive exactly
above the zero of the low wing. On a compact strictly dry interval the
finite positive horizontal length tends to zero. The sine projection of
the same joint limit therefore vanishes there. Exhausting the open dry
interval and removing its single zero endpoint leaves only positive
niche contacts. Positivity of the sine weight transfers this conclusion
to the unweighted joint measure. The final theorem derives its dry
interval from the actual low wing and the already proved first-unit
bound; no support or occupation premise is added to the tilted cap
problem.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

variable {target : Set Plane} {a b C h m c K : ℝ} {ρ : ℝ → ℝ}

/-- The open interval of the middle window of the tilted target above the zero of its low
wing. -/
def firstUnitPositiveInterval (U : Set Plane) (C : ℝ) : Set ℝ :=
  Ioo (max (-C) (companionZero (leftCompanionCap U (-C)))) C

/-- In the middle window, the niche is positive exactly above the zero of the low wing. -/
theorem IsTiltedFirstUnitTarget.positive_middle_eq
    (H : IsTiltedFirstUnitTarget target a b C h m c ρ K) :
    Ioo (-C) C ∩ {x | 0 < sweptNiche target (Real.pi / 2) x} = firstUnitPositiveInterval target C :=
  fullTiltedSupportQuarterPair_positive_middle_eq H.hU H.hm.le H.haffine H.hρ H.hρ0 H.hρK H.heq
    H.hl H.hr H.hC H.hm H.hheight H.hlow H.hhigh H.hh H.hunit

namespace AngularGrid.SelectedJointSourceLimit

variable (J : SelectedJointSourceLimit target a b)

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
  -- On a compact dry interval the finite positive horizontal length tends to zero.
  refine measure_restrict_Ioo_eq_of_Ioc fun x y hxy hsub => ?_
  have hL := (hmiddle (hsub (left_mem_Icc.2 hxy))).1
  have hR := (hmiddle (hsub (right_mem_Icc.2 hxy))).2
  have hzero := finitePositiveLength_tendsto_zero_on_dry_interval
    J.hausdorff J.isCap hTarget J.level_tendsto (show 0 ≤ |a| + |b| + 1 by positivity)
    (fun n => subset_symmetricBox_of_horizontalBox (J.selected n).inBox) hxy hL hR
    fun z hz => hnegative z (hsub hz)
  simp only [← integral_innerJointMeasure_sin _ _ hxy] at hzero
  change (J.horizontalProjection : Measure ℝ) (Ioc x y) = 0
  rw [← measureReal_eq_zero_iff (measure_ne_top _ _),
    J.horizontalProjection_real_eq_sine_integral measurableSet_Ioc]
  exact tendsto_nhds_unique (J.local_test_integral_tendsto hTarget sourceSineFunction hL hR)
    (hzero.mono_left sourceLimitFilter_le_atTop)

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
theorem ae_niche_pos (H : IsTiltedFirstUnitTarget target a b C h m c ρ K) :
    ∀ᵐ z ∂(J.measure : Measure Plane), 0 < sweptNiche target (Real.pi / 2) z.2 := by
  have haff : ∀ x ∈ Icc (-C) C, capRoof target x = m * x + c := H.middleHalfInterval_eq ▸ H.haffine
  obtain ⟨ha, hb⟩ := H.mem_horizontalProjection
  have hab : -C < C := by linarith only [H.hC]
  have hzaxis := (H.hU.isCap.leftCompanionCap ha).companionZero_lt_left_add_one
    (by rw [horizontalLeft_leftCompanionCap H.hU.isCap ha,
          H.hU.isCap.capRoof_leftCompanionCap ha ⟨le_rfl, by rw [H.hl]; linarith only [H.hC]⟩]
        exact (H.hU.endpoint_heights_pos_of_affine H.hheight ⟨m, c, H.haffine⟩).2)
  rw [horizontalLeft_leftCompanionCap H.hU.isCap ha] at hzaxis
  have hzC : companionZero (leftCompanionCap target (-C)) < C := by
    linarith only [hzaxis, H.hl, H.hC]
  filter_upwards [H.middle_eq ▸ J.ae_spatial_mem_open_middle H.hU.isCap,
    measure_eq_zero_iff_ae_notMem.mp (J.spatial_Ioo_eq_zero_of_dry H.hU.isCap (l := -C)
      (H.middle_eq ▸ Ioo_subset_Ioo le_rfl hzC.le) fun x hx t ht =>
        H.hU.isCap.secondWallNumerator_neg_of_lt_low_wing_zero ha hb hab haff H.hhigh
          (hx.2.trans hzC) hx.2 (hx.2.trans hzaxis) ht),
    measure_eq_zero_iff_ae_notMem.mp (J.spatial_fiber_eq_zero _)] with z hz hn hz₀
  refine (H.positive_middle_eq.ge ⟨max_lt hz.1 ?_, hz.2⟩).2
  exact (not_lt.1 fun h => hn ⟨mem_univ _, hz.1, h⟩).lt_of_ne fun h => hz₀ ⟨mem_univ _, h.symm⟩

end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
