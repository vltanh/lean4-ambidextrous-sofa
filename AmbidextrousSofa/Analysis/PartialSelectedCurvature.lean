module

public import AmbidextrousSofa.Analysis.PartialSelectedSequence
public import AmbidextrousSofa.Analysis.SelectedCurvature

@[expose] public section

/-!
# Actual selected proper-angle curvature atoms

The proper barrier retains the whole terminal wall in its literal
finite source expression. The existing finite spatial first variation
therefore bounds every selected curvature atom by its actual inner source,
uncharged middle facet mass, and summable persistent support error.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace PartialGrid

open FinitePolygon AngularGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

def outerDensity (U : Set Plane) (α : TerminalAngle) (grid : Finset QuarterAngle) (j : SourceIndex α grid) : ℝ → ℝ := by
  classical
  exact (roofExpr (ι := SourceIndex α grid)).sourceDensity (wallSlope (normal α grid))
    (roofIntercept (normal α grid) (fun i => support U (normal α grid i)))
    (outwardVelocity (normal α grid) j)

def innerDensity (U : Set Plane) (α : TerminalAngle)
    (hαL : (α : ℝ) < Real.pi / 2) (grid : Finset QuarterAngle) (j : SourceIndex α grid) : ℝ → ℝ := by
  classical
  exact (barrierExpr (pairList α grid) (some (terminalIndex α hαL grid))).sourceDensity (wallSlope (normal α grid))
    (barrierIntercept (normal α grid) (fun i => support U (normal α grid i)))
    (outwardVelocity (normal α grid) j)

theorem outerDensity_nonneg (U : Set Plane) (α : TerminalAngle) (grid : Finset QuarterAngle)
    (j : SourceIndex α grid) (x : ℝ) : 0 ≤ outerDensity U α grid j x := by
  classical
  exact outward_sourceDensity_nonneg _ _ _ _ (normal_snd_pos α grid j).le x

theorem innerDensity_nonneg (U : Set Plane) (α : TerminalAngle)
    (hαL : (α : ℝ) < Real.pi / 2) (grid : Finset QuarterAngle)
    (j : SourceIndex α grid) (x : ℝ) : 0 ≤ innerDensity U α hαL grid j x := by
  classical
  exact outward_sourceDensity_nonneg _ _ _ _ (normal_snd_pos α grid j).le x

theorem intervalIntegrable_outerDensity (U : Set Plane) (α : TerminalAngle) (grid : Finset QuarterAngle)
    (j : SourceIndex α grid) (a b : ℝ) : IntervalIntegrable (outerDensity U α grid j) volume a b := by
  classical
  exact intervalIntegrable_outward_sourceDensity _ _ _ _ a b

theorem intervalIntegrable_innerDensity (U : Set Plane) (α : TerminalAngle)
    (hαL : (α : ℝ) < Real.pi / 2) (grid : Finset QuarterAngle)
    (j : SourceIndex α grid) (a b : ℝ) : IntervalIntegrable (innerDensity U α hαL grid j) volume a b := by
  classical
  exact intervalIntegrable_outward_sourceDensity _ _ _ _ a b

def selectionDefect (target U : Set Plane) (α : TerminalAngle) (level : ℕ) (coefficient : ℝ)
    (j : SourceIndex α (dyadic level)) : ℝ :=
  2 * coefficient * stageWeight α level j *
    |support U (normal α (dyadic level) j) - support target (normal α (dyadic level) j)|

theorem selectionDefect_nonneg (target U : Set Plane) (α : TerminalAngle) (level : ℕ)
    {coefficient : ℝ} (hcoefficient : 0 ≤ coefficient) (j : SourceIndex α (dyadic level)) :
    0 ≤ selectionDefect target U α level coefficient j := by
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hcoefficient)
    (stageWeight_nonneg α level j)) (abs_nonneg _)

/-- The actual source atom estimate. A zero atom is included without
requiring a positive-face variation. -/
theorem IsSelectedPolygon.curvature_atom_le {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U) (hcoefficient : 0 ≤ coefficient)
    (j : SourceIndex α (dyadic level)) :
    (upperCurvature U {fullAngle α (dyadic level) j}).toReal ≤
      (∫ x in (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)..
        (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4),
        innerDensity U α hαL (dyadic level) j x) +
      (∫ x in (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)..
        (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4),
        outerDensity U α (dyadic level) j x) + selectionDefect target U α level coefficient j := by
  classical
  let grid := dyadic level
  let θ := fullAngle α grid j
  let height : SourceIndex α grid → ℝ := fun i => support U (normal α grid i)
  let weight : SourceIndex α grid → ℝ := fun i => coefficient * stageWeight α level i
  let prescribed : SourceIndex α grid → ℝ := fun i => support target (normal α grid i)
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  have hmiddle : horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 ≤
      horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 := by linarith
  by_cases hmass : 0 < (upperCurvature U {θ}).toReal
  · have hcb := hU.isCap.imported_isConvexBody
    have hp := MovingSofaOptimality.vminus_mem_edge hcb θ
    have hq := MovingSofaOptimality.vplus_mem_edge hcb θ
    have hpq : MovingSofaOptimality.vminus U θ ≠ MovingSofaOptimality.vplus U θ := by
      intro heq
      have hzero : (upperCurvature U {θ}).toReal = 0 := by
        change MovingSofaOptimality.sigmaAt U θ = 0
        rw [(MovingSofaOptimality.proposition2_1_2 hcb θ).1, heq, sub_self]
        simp [MovingSofaOptimality.norm2, MovingSofaOptimality.dot]
      linarith
    have hmax : ∀ V : Set Plane, IsDownwardCap V →
        horizontalProjection V = Icc (horizontalLeft U) (horizontalRight U) →
        finiteSpatialScore V (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)) -
          sampledPenalty V (normal α grid) weight prescribed ≤
        finiteSpatialScore (circumscription U (normal α grid)) (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)) -
          sampledPenalty (circumscription U (normal α grid)) (normal α grid) weight prescribed := by
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
      have h' : finiteSpatialScore V (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)) -
          sampledPenalty V (normal α grid) weight prescribed ≤
          finiteSpatialScore U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)) -
            sampledPenalty U (normal α grid) weight prescribed := by
        simpa only [score, weight, prescribed, sampledPenalty_mul,
          sampledPenalty_eq_stagePenalty, grid] using h
      exact h'.trans_eq (congrArg (fun K => finiteSpatialScore K (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)) -
        sampledPenalty K (normal α grid) weight prescribed) hU.polygon_eq)
    have hExpose := selected_polygon_exposure_inequality (normal α grid) height weight prescribed
      (pairList α grid) (some (terminalIndex α hαL grid)) j hlr (normal_snd_pos α grid) (wallSlopes_injective α grid)
      (circumscription_baseline hU.isCap (normal α grid))
      (support_circumscription hU.isCap (normal α grid))
      (subset_circumscription hU.isCap (normal α grid) hp.1)
      (subset_circumscription hU.isCap (normal α grid) hq.1) hpq
      (by simpa only [height, normal_eq_unitNormal] using hp.2)
      (by simpa only [height, normal_eq_unitNormal] using hq.2)
      (normal_fst_ne_zero α grid j)
      (fun i hij => AngularGrid.normal_det_ne_zero (outerGrid α grid) (Ne.symm hij)) (normal_unit α grid j) hmax
    have htotal := integral_outerSource_eq_curvature_atom hU.isCap (normal α grid)
      (normal_snd_pos α grid) (wallSlopes_injective α grid) hU.polygon_eq j
      (normal_eq_unitNormal α grid j)
    have hfirst := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_outerDensity U α grid j (horizontalLeft U)
        (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4))
      (intervalIntegrable_outerDensity U α grid j
        (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)
        (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4))
    have hlast := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_outerDensity U α grid j (horizontalLeft U)
        (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4))
      (intervalIntegrable_outerDensity U α grid j
        (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) (horizontalRight U))
    have hdefect : 2 * weight j * (height j - prescribed j) ≤
        selectionDefect target U α level coefficient j := by
      have h := mul_le_mul_of_nonneg_left (le_abs_self (height j - prescribed j))
        (mul_nonneg (by norm_num) (mul_nonneg hcoefficient (stageWeight_nonneg α level j)))
      simpa only [weight, height, prescribed, selectionDefect, grid, mul_assoc] using h
    change (∫ x in (horizontalLeft U)..(horizontalRight U), outerDensity U α grid j x) =
      (upperCurvature U {θ}).toReal at htotal
    change (∫ x in (horizontalLeft U)..
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4), outerDensity U α grid j x) +
      (∫ x in (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4)..
        (horizontalRight U), outerDensity U α grid j x) ≤
      (∫ x in (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)..
        (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4),
        innerDensity U α hαL grid j x) + 2 * weight j * (height j - prescribed j) at hExpose
    change (upperCurvature U {θ}).toReal ≤ _
    nlinarith
  · have hInner := intervalIntegral.integral_nonneg_of_forall hmiddle (innerDensity_nonneg U α hαL grid j)
    have hOuter := intervalIntegral.integral_nonneg_of_forall hmiddle (outerDensity_nonneg U α grid j)
    have hDefect := selectionDefect_nonneg target U α level hcoefficient j
    change (upperCurvature U {θ}).toReal ≤ _
    linarith [le_of_not_gt hmass]

theorem sum_selectionDefect_le {target U : Set Plane}
    (hTarget : IsDownwardCap target) (hU : IsDownwardCap U) (α : TerminalAngle) (level : ℕ)
    {coefficient : ℝ} (hcoefficient : 0 ≤ coefficient) :
    (∑ j, selectionDefect target U α level coefficient j) ≤
      4 * coefficient * Metric.hausdorffDist U target := by
  classical
  have hpoint : ∀ j : SourceIndex α (dyadic level),
      |support U (normal α (dyadic level) j) - support target (normal α (dyadic level) j)| ≤
        2 * Metric.hausdorffDist U target := by
    intro j
    have h := abs_support_sub_le_hausdorff hU.isCompact hU.nonempty
      hTarget.isCompact hTarget.nonempty (normal α (dyadic level) j)
    have hn : |(normal α (dyadic level) j).1| + |(normal α (dyadic level) j).2| ≤ 2 := by
      simp only [normal_eq_unitNormal]
      change |Real.cos _| + |Real.sin _| ≤ 2
      linarith [Real.abs_cos_le_one (fullAngle α (dyadic level) j),
        Real.abs_sin_le_one (fullAngle α (dyadic level) j)]
    have hmul := mul_le_mul_of_nonneg_left hn
      (Metric.hausdorffDist_nonneg (s := U) (t := target))
    exact h.trans (by linarith)
  calc
    (∑ j, selectionDefect target U α level coefficient j) ≤
        ∑ j, 4 * coefficient * Metric.hausdorffDist U target * stageWeight α level j := by
      apply Finset.sum_le_sum
      intro j _
      have h := mul_le_mul_of_nonneg_left (hpoint j)
        (mul_nonneg (mul_nonneg (by norm_num) hcoefficient) (stageWeight_nonneg α level j))
      dsimp only [selectionDefect]
      nlinarith
    _ = 4 * coefficient * Metric.hausdorffDist U target * ∑ j, stageWeight α level j := by
      rw [Finset.mul_sum]
    _ ≤ 4 * coefficient * Metric.hausdorffDist U target := by
      have h := mul_le_mul_of_nonneg_left (sum_stageWeight_le_one α level)
        (mul_nonneg (mul_nonneg (by norm_num) hcoefficient) Metric.hausdorffDist_nonneg)
      simpa only [mul_one] using h

/-- All the finite support defects disappear in the actual selected
limit; their number may grow without bound. -/
theorem selectionDefect_sum_tendsto {target : Set Plane} {U : ℕ → Set Plane}
    (hTarget : IsDownwardCap target) (hU : ∀ n, IsDownwardCap (U n))
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ} (hcoefficient : ∀ n, 0 ≤ coefficient n)
    (hrate : Tendsto coefficient atTop (𝓝 0)) (hHausdorff : CapHausdorffTendsto U target) :
    Tendsto (fun n => ∑ j, selectionDefect target (U n) α (level n) (coefficient n) j)
      atTop (𝓝 0) := by
  apply squeeze_zero
    (fun n => Finset.sum_nonneg (fun j _ =>
      selectionDefect_nonneg target (U n) α (level n) (hcoefficient n) j))
    (fun n => sum_selectionDefect_le hTarget (hU n) α (level n) (hcoefficient n))
  simpa only [mul_zero] using (hrate.const_mul 4).mul hHausdorff

end PartialGrid

end AmbidextrousSofa
