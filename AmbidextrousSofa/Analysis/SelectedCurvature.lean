module

public import AmbidextrousSofa.Analysis.FacetCurvature

@[expose] public section

/-!
# Actual selected curvature atoms with the uncharged middle face retained

Only the exterior roof is charged by the spatial score. Consequently its
finite variation controls the entire curvature atom after adding back the
actual middle part of that outer facet. This term is retained explicitly;
it is not erased by an angular objective or an assumed regularity field.
The support-penalty errors have a proved summable bound tending to zero
along the actual selected sequence.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace FinitePolygon

variable {ι : Type*}

theorem outward_sourceDensity_nonneg [DecidableEq ι] (e : WallExpr (Option ι))
    (normal : ι → Plane) (intercept : Option ι → ℝ) (j : ι)
    (hny : 0 ≤ (normal j).2) (x : ℝ) :
    0 ≤ e.sourceDensity (wallSlope normal) intercept (outwardVelocity normal j) x := by
  rw [outwardVelocity_eq_single, e.sourceDensity_single]
  exact Set.indicator_nonneg (fun _ _ => div_nonneg (by norm_num) hny) x

theorem intervalIntegrable_outward_sourceDensity [DecidableEq ι]
    (e : WallExpr (Option ι)) (normal : ι → Plane) (intercept : Option ι → ℝ)
    (j : ι) (a b : ℝ) :
    IntervalIntegrable (e.sourceDensity (wallSlope normal) intercept (outwardVelocity normal j))
      volume a b := by
  rw [outwardVelocity_eq_single, e.sourceDensity_single]
  exact (continuous_const.integrableOn_uIcc.indicator
    (e.measurableSet_sourceSet _ _ _)).intervalIntegrable

end FinitePolygon

namespace AngularGrid

open FinitePolygon

def outerDensity (U : Set Plane) (grid : Finset QuarterAngle) (j : SourceIndex grid) : ℝ → ℝ := by
  classical
  exact (roofExpr (ι := SourceIndex grid)).sourceDensity (wallSlope (normal grid))
    (roofIntercept (normal grid) (fun i => support U (normal grid i)))
    (outwardVelocity (normal grid) j)

def innerDensity (U : Set Plane) (grid : Finset QuarterAngle) (j : SourceIndex grid) : ℝ → ℝ := by
  classical
  exact (barrierExpr (pairList grid) none).sourceDensity (wallSlope (normal grid))
    (barrierIntercept (normal grid) (fun i => support U (normal grid i)))
    (outwardVelocity (normal grid) j)

theorem outerDensity_nonneg (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex grid) (x : ℝ) : 0 ≤ outerDensity U grid j x :=
  outward_sourceDensity_nonneg _ _ _ _ (normal_snd_pos grid j).le x

theorem innerDensity_nonneg (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex grid) (x : ℝ) : 0 ≤ innerDensity U grid j x :=
  outward_sourceDensity_nonneg _ _ _ _ (normal_snd_pos grid j).le x

theorem intervalIntegrable_outerDensity (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex grid) (a b : ℝ) : IntervalIntegrable (outerDensity U grid j) volume a b :=
  intervalIntegrable_outward_sourceDensity _ _ _ _ a b

theorem intervalIntegrable_innerDensity (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex grid) (a b : ℝ) : IntervalIntegrable (innerDensity U grid j) volume a b :=
  intervalIntegrable_outward_sourceDensity _ _ _ _ a b

def selectionDefect (target U : Set Plane) (level : ℕ) (coefficient : ℝ)
    (j : SourceIndex (dyadic level)) : ℝ :=
  2 * coefficient * stageWeight level j *
    |support U (normal (dyadic level) j) - support target (normal (dyadic level) j)|

theorem selectionDefect_nonneg (target U : Set Plane) (level : ℕ)
    {coefficient : ℝ} (hcoefficient : 0 ≤ coefficient) (j : SourceIndex (dyadic level)) :
    0 ≤ selectionDefect target U level coefficient j :=
  mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hcoefficient) (stageWeight_nonneg level j))
    (abs_nonneg _)

/-- The actual source atom estimate. A zero atom is included without
requiring a positive-face variation. -/
theorem IsSelectedPolygon.curvature_atom_le {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hcoefficient : 0 ≤ coefficient)
    (j : SourceIndex (dyadic level)) :
    (upperCurvature U {fullAngle (dyadic level) j}).toReal ≤
      (∫ x in (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)..
        (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4),
        innerDensity U (dyadic level) j x) +
      (∫ x in (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)..
        (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4),
        outerDensity U (dyadic level) j x) + selectionDefect target U level coefficient j := by
  classical
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  rcases ENNReal.toReal_nonneg.eq_or_lt with hmass | hmass
  · have hmiddle : horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 ≤
        horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 := by linarith
    rw [← hmass]
    linarith [intervalIntegral.integral_nonneg_of_forall (μ := volume) hmiddle
      (innerDensity_nonneg U (dyadic level) j), intervalIntegral.integral_nonneg_of_forall
      (μ := volume) hmiddle (outerDensity_nonneg U (dyadic level) j),
      selectionDefect_nonneg target U level hcoefficient j]
  have hcb := hU.isCap.imported_isConvexBody
  have hp := MovingSofaOptimality.vminus_mem_edge hcb (fullAngle (dyadic level) j)
  have hq := MovingSofaOptimality.vplus_mem_edge hcb (fullAngle (dyadic level) j)
  have hpq : MovingSofaOptimality.vminus U (fullAngle (dyadic level) j) ≠
      MovingSofaOptimality.vplus U (fullAngle (dyadic level) j) := fun heq => hmass.ne' <| by
    change MovingSofaOptimality.sigmaAt U _ = 0
    rw [(MovingSofaOptimality.proposition2_1_2 hcb _).1, heq, sub_self]
    simp [MovingSofaOptimality.norm2, MovingSofaOptimality.dot]
  have hExpose := selected_polygon_exposure_inequality (normal (dyadic level)) _
    (fun i => coefficient * stageWeight level i) (fun i => support target (normal (dyadic level) i))
    (pairList (dyadic level)) none j hlr (normal_snd_pos _) (wallSlopes_injective _)
    (circumscription_baseline hU.isCap _) (support_circumscription hU.isCap _)
    (subset_circumscription hU.isCap _ hp.1) (subset_circumscription hU.isCap _ hq.1) hpq
    (by rw [normal_eq_unitNormal]; exact hp.2) (by rw [normal_eq_unitNormal]; exact hq.2)
    (normal_fst_ne_zero _ j) (fun i hij => normal_det_ne_zero _ (Ne.symm hij)) (normal_unit _ j)
    fun V hV hproj => by
      have hVB : V ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 := fun p hpV => by
        have hx : p.1 ∈ horizontalProjection U := by
          rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex,
            ← hproj]
          exact ⟨p, hpV, rfl⟩
        obtain ⟨q, hqU, hqx⟩ := hx
        exact ⟨hqx ▸ (hU.inBox hqU).1, hV.inStrip hpV⟩
      rw [show upperPolygon _ _ _ _ = U from hU.polygon_eq.symm]
      simpa only [score, stagePenalty, sampledPenalty_mul] using hU.maximizes V hV hVB
  have htotal := integral_outerSource_eq_curvature_atom hU.isCap (normal (dyadic level))
    (normal_snd_pos _) (wallSlopes_injective _) hU.polygon_eq j (normal_eq_unitNormal _ j)
  have hfirst := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_outerDensity U (dyadic level) j (horizontalLeft U)
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4))
    (intervalIntegrable_outerDensity U (dyadic level) j _
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4))
  have hlast := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_outerDensity U (dyadic level) j (horizontalLeft U)
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4))
    (intervalIntegrable_outerDensity U (dyadic level) j _ (horizontalRight U))
  unfold outerDensity innerDensity selectionDefect at *
  linarith [mul_le_mul_of_nonneg_left (le_abs_self (support U (normal (dyadic level) j) -
    support target (normal (dyadic level) j))) (mul_nonneg hcoefficient (stageWeight_nonneg level j))]

theorem sum_selectionDefect_le {target U : Set Plane}
    (hTarget : IsDownwardCap target) (hU : IsDownwardCap U) (level : ℕ)
    {coefficient : ℝ} (hcoefficient : 0 ≤ coefficient) :
    (∑ j, selectionDefect target U level coefficient j) ≤
      4 * coefficient * Metric.hausdorffDist U target := by
  classical
  have hd := Metric.hausdorffDist_nonneg (s := U) (t := target)
  calc (∑ j, selectionDefect target U level coefficient j)
      ≤ ∑ j, 4 * coefficient * Metric.hausdorffDist U target * stageWeight level j := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hn : |(normal (dyadic level) j).1| + |(normal (dyadic level) j).2| ≤ 2 := by
          rw [normal_eq_unitNormal]
          exact (add_le_add (Real.abs_cos_le_one _) (Real.abs_sin_le_one _)).trans_eq
            one_add_one_eq_two
        have h := (abs_support_sub_le_hausdorff hU.isCompact hU.nonempty hTarget.isCompact
          hTarget.nonempty (normal (dyadic level) j)).trans (mul_le_mul_of_nonneg_left hn hd)
        have := mul_le_mul_of_nonneg_left h (mul_nonneg hcoefficient (stageWeight_nonneg level j))
        unfold selectionDefect
        linarith
    _ = 4 * coefficient * Metric.hausdorffDist U target * ∑ j, stageWeight level j := by
        rw [Finset.mul_sum]
    _ ≤ 4 * coefficient * Metric.hausdorffDist U target :=
        mul_le_of_le_one_right (mul_nonneg (mul_nonneg zero_le_four hcoefficient) hd)
          (sum_stageWeight_le_one level)

/-- All the finite support defects disappear in the actual selected
limit; their number may grow without bound. -/
theorem selectionDefect_sum_tendsto {target : Set Plane} {U : ℕ → Set Plane}
    (hTarget : IsDownwardCap target) (hU : ∀ n, IsDownwardCap (U n))
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ} (hcoefficient : ∀ n, 0 ≤ coefficient n)
    (hrate : Tendsto coefficient atTop (𝓝 0)) (hHausdorff : CapHausdorffTendsto U target) :
    Tendsto (fun n => ∑ j, selectionDefect target (U n) (level n) (coefficient n) j)
      atTop (𝓝 0) := by
  apply squeeze_zero
    (fun n => Finset.sum_nonneg (fun j _ =>
      selectionDefect_nonneg target (U n) (level n) (hcoefficient n) j))
    (fun n => sum_selectionDefect_le hTarget (hU n) (level n) (hcoefficient n))
  simpa only [mul_zero] using (hrate.const_mul 4).mul hHausdorff

end AngularGrid

end AmbidextrousSofa
