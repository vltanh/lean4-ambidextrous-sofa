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
    (j : SourceIndex α grid) (x : ℝ) : 0 ≤ outerDensity U α grid j x :=
  outward_sourceDensity_nonneg _ _ _ _ (normal_snd_pos α grid j).le x

theorem innerDensity_nonneg (U : Set Plane) (α : TerminalAngle)
    (hαL : (α : ℝ) < Real.pi / 2) (grid : Finset QuarterAngle)
    (j : SourceIndex α grid) (x : ℝ) : 0 ≤ innerDensity U α hαL grid j x :=
  outward_sourceDensity_nonneg _ _ _ _ (normal_snd_pos α grid j).le x

theorem intervalIntegrable_outerDensity (U : Set Plane) (α : TerminalAngle) (grid : Finset QuarterAngle)
    (j : SourceIndex α grid) (a b : ℝ) : IntervalIntegrable (outerDensity U α grid j) volume a b :=
  intervalIntegrable_outward_sourceDensity _ _ _ _ a b

def selectionDefect (target U : Set Plane) (α : TerminalAngle) (level : ℕ) (coefficient : ℝ)
    (j : SourceIndex α (dyadic level)) : ℝ :=
  2 * coefficient * stageWeight α level j *
    |support U (normal α (dyadic level) j) - support target (normal α (dyadic level) j)|

theorem selectionDefect_nonneg (target U : Set Plane) (α : TerminalAngle) (level : ℕ)
    {coefficient : ℝ} (hcoefficient : 0 ≤ coefficient) (j : SourceIndex α (dyadic level)) :
    0 ≤ selectionDefect target U α level coefficient j :=
  mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hcoefficient) (stageWeight_nonneg α level j))
    (abs_nonneg _)

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
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  rcases ENNReal.toReal_nonneg.eq_or_lt with hmass | hmass
  · have hmiddle : horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 ≤
        horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 := by linarith
    rw [← hmass]
    linarith [intervalIntegral.integral_nonneg_of_forall (μ := volume) hmiddle
      (innerDensity_nonneg U α hαL (dyadic level) j), intervalIntegral.integral_nonneg_of_forall
      (μ := volume) hmiddle (outerDensity_nonneg U α (dyadic level) j),
      selectionDefect_nonneg target U α level hcoefficient j]
  have hcb := hU.isCap.imported_isConvexBody
  have hp := MovingSofaOptimality.vminus_mem_edge hcb (fullAngle α (dyadic level) j)
  have hq := MovingSofaOptimality.vplus_mem_edge hcb (fullAngle α (dyadic level) j)
  have hpq : MovingSofaOptimality.vminus U (fullAngle α (dyadic level) j) ≠
      MovingSofaOptimality.vplus U (fullAngle α (dyadic level) j) := fun heq => hmass.ne' <| by
    change MovingSofaOptimality.sigmaAt U _ = 0
    rw [(MovingSofaOptimality.proposition2_1_2 hcb _).1, heq, sub_self]
    simp [MovingSofaOptimality.norm2, MovingSofaOptimality.dot]
  have hExpose := selected_polygon_exposure_inequality (normal α (dyadic level)) _
    (fun i => coefficient * stageWeight α level i)
    (fun i => support target (normal α (dyadic level) i)) (pairList α (dyadic level))
    (some (terminalIndex α hαL (dyadic level))) j hlr (normal_snd_pos _ _)
    (wallSlopes_injective _ _) (circumscription_baseline hU.isCap _)
    (support_circumscription hU.isCap _) (subset_circumscription hU.isCap _ hp.1)
    (subset_circumscription hU.isCap _ hq.1) hpq (by rw [normal_eq_unitNormal]; exact hp.2)
    (by rw [normal_eq_unitNormal]; exact hq.2) (normal_fst_ne_zero _ _ j)
    (fun i hij => AngularGrid.normal_det_ne_zero _ (Ne.symm hij)) (normal_unit _ _ j)
    fun V hV hproj => by
      have hVB : V ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 := fun p hpV => by
        have hx : p.1 ∈ horizontalProjection U := by
          rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex,
            ← hproj]
          exact ⟨p, hpV, rfl⟩
        obtain ⟨q, hqU, hqx⟩ := hx
        exact ⟨hqx ▸ (hU.inBox hqU).1, hV.inStrip hpV⟩
      rw [show upperPolygon _ _ _ _ = U from hU.polygon_eq.symm]
      simpa only [score, sampledPenalty_mul, sampledPenalty_eq_stagePenalty] using
        hU.maximizes V hV hVB
  have htotal := integral_outerSource_eq_curvature_atom hU.isCap (normal α (dyadic level))
    (normal_snd_pos _ _) (wallSlopes_injective _ _) hU.polygon_eq j (normal_eq_unitNormal _ _ j)
  have hfirst := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_outerDensity U α (dyadic level) j (horizontalLeft U)
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4))
    (intervalIntegrable_outerDensity U α (dyadic level) j _
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4))
  have hlast := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_outerDensity U α (dyadic level) j (horizontalLeft U)
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4))
    (intervalIntegrable_outerDensity U α (dyadic level) j _ (horizontalRight U))
  unfold outerDensity innerDensity selectionDefect at *
  linarith [mul_le_mul_of_nonneg_left (le_abs_self (support U (normal α (dyadic level) j) -
    support target (normal α (dyadic level) j)))
      (mul_nonneg hcoefficient (stageWeight_nonneg α level j))]

theorem sum_selectionDefect_le {target U : Set Plane}
    (hTarget : IsDownwardCap target) (hU : IsDownwardCap U) (α : TerminalAngle) (level : ℕ)
    {coefficient : ℝ} (hcoefficient : 0 ≤ coefficient) :
    (∑ j, selectionDefect target U α level coefficient j) ≤
      4 * coefficient * Metric.hausdorffDist U target := by
  classical
  have hd := Metric.hausdorffDist_nonneg (s := U) (t := target)
  calc (∑ j, selectionDefect target U α level coefficient j)
      ≤ ∑ j, 4 * coefficient * Metric.hausdorffDist U target * stageWeight α level j := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hn : |(normal α (dyadic level) j).1| + |(normal α (dyadic level) j).2| ≤ 2 := by
          rw [normal_eq_unitNormal]
          exact (add_le_add (Real.abs_cos_le_one _) (Real.abs_sin_le_one _)).trans_eq
            one_add_one_eq_two
        have h := (abs_support_sub_le_hausdorff hU.isCompact hU.nonempty hTarget.isCompact
          hTarget.nonempty (normal α (dyadic level) j)).trans (mul_le_mul_of_nonneg_left hn hd)
        have := mul_le_mul_of_nonneg_left h
          (mul_nonneg hcoefficient (stageWeight_nonneg α level j))
        unfold selectionDefect
        linarith
    _ = 4 * coefficient * Metric.hausdorffDist U target * ∑ j, stageWeight α level j := by
        rw [Finset.mul_sum]
    _ ≤ 4 * coefficient * Metric.hausdorffDist U target :=
        mul_le_of_le_one_right (mul_nonneg (mul_nonneg zero_le_four hcoefficient) hd)
          (sum_stageWeight_le_one α level)

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
