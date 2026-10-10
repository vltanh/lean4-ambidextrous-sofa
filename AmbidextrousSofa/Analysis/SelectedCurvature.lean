import AmbidextrousSofa.Analysis.FacetCurvature

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
  apply intervalIntegrable_iff'.mpr
  have hconst : IntegrableOn (fun _ : ℝ => 1 / (normal j).2) (uIcc a b) := by
    simpa only [uIcc] using
      (continuous_const.integrableOn_Icc :
        IntegrableOn (fun _ : ℝ => 1 / (normal j).2) (Icc (min a b) (max a b)))
  exact hconst.indicator (e.measurableSet_sourceSet _ _ _)

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
    (j : SourceIndex grid) (x : ℝ) : 0 ≤ outerDensity U grid j x := by
  classical
  exact outward_sourceDensity_nonneg _ _ _ _ (normal_snd_pos grid j).le x

theorem innerDensity_nonneg (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex grid) (x : ℝ) : 0 ≤ innerDensity U grid j x := by
  classical
  exact outward_sourceDensity_nonneg _ _ _ _ (normal_snd_pos grid j).le x

theorem intervalIntegrable_outerDensity (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex grid) (a b : ℝ) : IntervalIntegrable (outerDensity U grid j) volume a b := by
  classical
  exact intervalIntegrable_outward_sourceDensity _ _ _ _ a b

theorem intervalIntegrable_innerDensity (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex grid) (a b : ℝ) : IntervalIntegrable (innerDensity U grid j) volume a b := by
  classical
  exact intervalIntegrable_outward_sourceDensity _ _ _ _ a b

def selectionDefect (target U : Set Plane) (level : ℕ) (coefficient : ℝ)
    (j : SourceIndex (dyadic level)) : ℝ :=
  2 * coefficient * stageWeight level j *
    |support U (normal (dyadic level) j) - support target (normal (dyadic level) j)|

theorem selectionDefect_nonneg (target U : Set Plane) (level : ℕ)
    {coefficient : ℝ} (hcoefficient : 0 ≤ coefficient) (j : SourceIndex (dyadic level)) :
    0 ≤ selectionDefect target U level coefficient j := by
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hcoefficient)
    (stageWeight_nonneg level j)) (abs_nonneg _)

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
  let grid := dyadic level
  let θ := fullAngle grid j
  let height : SourceIndex grid → ℝ := fun i => support U (normal grid i)
  let weight : SourceIndex grid → ℝ := fun i => coefficient * stageWeight level i
  let prescribed : SourceIndex grid → ℝ := fun i => support target (normal grid i)
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  have hmiddle : horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 ≤
      horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 := by linarith
  by_cases hmass : 0 < (upperCurvature U {θ}).toReal
  · have hcb := hU.isCap.imported_isConvexBody
    have hp := Imported.vminus_mem_edge hcb θ
    have hq := Imported.vplus_mem_edge hcb θ
    have hpq : Imported.vminus U θ ≠ Imported.vplus U θ := by
      intro heq
      have hzero : (upperCurvature U {θ}).toReal = 0 := by
        change Imported.sigmaAt U θ = 0
        rw [(Imported.proposition2_1_2 hcb θ).1, heq, sub_self]
        simp [Imported.norm2, Imported.dot]
      linarith
    have hmax : ∀ V : Set Plane, IsDownwardCap V →
        horizontalProjection V = Icc (horizontalLeft U) (horizontalRight U) →
        finiteSpatialScore V (normal grid) (pairList grid) none -
          sampledPenalty V (normal grid) weight prescribed ≤
        finiteSpatialScore (circumscription U (normal grid)) (normal grid) (pairList grid) none -
          sampledPenalty (circumscription U (normal grid)) (normal grid) weight prescribed := by
      intro V hV hprojection
      have hVB : V ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 := by
        intro p hpV
        have hx : p.1 ∈ Icc (horizontalLeft U) (horizontalRight U) := by
          rw [← hprojection]
          exact ⟨p, hpV, rfl⟩
        rw [← horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex] at hx
        obtain ⟨q, hqU, hqx⟩ := hx
        exact ⟨by simpa only [hqx] using (hU.inBox hqU).1, hV.inStrip hpV⟩
      have h := hU.maximizes V hV hVB
      have h' : finiteSpatialScore V (normal grid) (pairList grid) none -
          sampledPenalty V (normal grid) weight prescribed ≤
          finiteSpatialScore U (normal grid) (pairList grid) none -
            sampledPenalty U (normal grid) weight prescribed := by
        simpa only [score, stagePenalty, weight, prescribed, sampledPenalty_mul, grid] using h
      exact h'.trans_eq (congrArg (fun K => finiteSpatialScore K (normal grid) (pairList grid) none -
        sampledPenalty K (normal grid) weight prescribed) hU.polygon_eq)
    have hExpose := selected_polygon_exposure_inequality (normal grid) height weight prescribed
      (pairList grid) none j hlr (normal_snd_pos grid) (wallSlopes_injective grid)
      (circumscription_baseline hU.isCap (normal grid))
      (support_circumscription hU.isCap (normal grid))
      (subset_circumscription hU.isCap (normal grid) hp.1)
      (subset_circumscription hU.isCap (normal grid) hq.1) hpq
      (by simpa only [height, normal_eq_unitNormal] using hp.2)
      (by simpa only [height, normal_eq_unitNormal] using hq.2)
      (normal_fst_ne_zero grid j)
      (fun i hij => normal_det_ne_zero grid (Ne.symm hij)) (normal_unit grid j) hmax
    have htotal := integral_outerSource_eq_curvature_atom hU.isCap (normal grid)
      (normal_snd_pos grid) (wallSlopes_injective grid) hU.polygon_eq j
      (normal_eq_unitNormal grid j)
    have hfirst := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_outerDensity U grid j (horizontalLeft U)
        (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4))
      (intervalIntegrable_outerDensity U grid j
        (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)
        (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4))
    have hlast := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_outerDensity U grid j (horizontalLeft U)
        (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4))
      (intervalIntegrable_outerDensity U grid j
        (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) (horizontalRight U))
    have hdefect : 2 * weight j * (height j - prescribed j) ≤
        selectionDefect target U level coefficient j := by
      have h := mul_le_mul_of_nonneg_left (le_abs_self (height j - prescribed j))
        (mul_nonneg (by norm_num) (mul_nonneg hcoefficient (stageWeight_nonneg level j)))
      simpa only [weight, height, prescribed, selectionDefect, grid, mul_assoc] using h
    change (∫ x in (horizontalLeft U)..(horizontalRight U), outerDensity U grid j x) =
      (upperCurvature U {θ}).toReal at htotal
    change (∫ x in (horizontalLeft U)..
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4), outerDensity U grid j x) +
      (∫ x in (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4)..
        (horizontalRight U), outerDensity U grid j x) ≤
      (∫ x in (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)..
        (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4),
        innerDensity U grid j x) + 2 * weight j * (height j - prescribed j) at hExpose
    change (upperCurvature U {θ}).toReal ≤ _
    nlinarith
  · have hInner := intervalIntegral.integral_nonneg_of_forall hmiddle (innerDensity_nonneg U grid j)
    have hOuter := intervalIntegral.integral_nonneg_of_forall hmiddle (outerDensity_nonneg U grid j)
    have hDefect := selectionDefect_nonneg target U level hcoefficient j
    change (upperCurvature U {θ}).toReal ≤ _
    linarith [le_of_not_gt hmass]

theorem sum_selectionDefect_le {target U : Set Plane}
    (hTarget : IsDownwardCap target) (hU : IsDownwardCap U) (level : ℕ)
    {coefficient : ℝ} (hcoefficient : 0 ≤ coefficient) :
    (∑ j, selectionDefect target U level coefficient j) ≤
      4 * coefficient * Metric.hausdorffDist U target := by
  classical
  have hpoint : ∀ j : SourceIndex (dyadic level),
      |support U (normal (dyadic level) j) - support target (normal (dyadic level) j)| ≤
        2 * Metric.hausdorffDist U target := by
    intro j
    have h := abs_support_sub_le_hausdorff hU.isCompact hU.nonempty
      hTarget.isCompact hTarget.nonempty (normal (dyadic level) j)
    have hn : |(normal (dyadic level) j).1| + |(normal (dyadic level) j).2| ≤ 2 := by
      simp only [normal_eq_unitNormal]
      change |Real.cos _| + |Real.sin _| ≤ 2
      linarith [Real.abs_cos_le_one (fullAngle (dyadic level) j),
        Real.abs_sin_le_one (fullAngle (dyadic level) j)]
    have hmul := mul_le_mul_of_nonneg_left hn
      (Metric.hausdorffDist_nonneg (s := U) (t := target))
    exact h.trans (by linarith)
  calc
    (∑ j, selectionDefect target U level coefficient j) ≤
        ∑ j, 4 * coefficient * Metric.hausdorffDist U target * stageWeight level j := by
      apply Finset.sum_le_sum
      intro j _
      have h := mul_le_mul_of_nonneg_left (hpoint j)
        (mul_nonneg (mul_nonneg (by norm_num) hcoefficient) (stageWeight_nonneg level j))
      dsimp only [selectionDefect]
      nlinarith
    _ = 4 * coefficient * Metric.hausdorffDist U target * ∑ j, stageWeight level j := by
      rw [Finset.mul_sum]
    _ ≤ 4 * coefficient * Metric.hausdorffDist U target := by
      have h := mul_le_mul_of_nonneg_left (sum_stageWeight_le_one level)
        (mul_nonneg (mul_nonneg (by norm_num) hcoefficient) Metric.hausdorffDist_nonneg)
      simpa only [mul_one] using h

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
