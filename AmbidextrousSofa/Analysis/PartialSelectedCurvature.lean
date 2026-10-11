module

public import AmbidextrousSofa.Analysis.PartialSelectedSequence
public import AmbidextrousSofa.Analysis.SelectedCurvature

@[expose] public section

/-!
# Actual selected proper-angle curvature atoms

The proper barrier retains the whole terminal wall in its literal
finite source expression. The finite spatial first variation, proved for
every grid, therefore bounds every selected curvature atom by its actual
inner source, uncharged middle facet mass, and summable persistent
support error.
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
        outerDensity U α (dyadic level) j x) + selectionDefect target U α level coefficient j :=
  curvature_atom_le_of_maximizes (s := fun i => support target (normal α (dyadic level) i))
    (pairList α (dyadic level)) (some (terminalIndex α hαL (dyadic level))) hU.isCap hU.inBox
    hU.polygon_eq hcoefficient (stageWeight_nonneg α level) (fun V hV hVB => by
      have h := hU.maximizes V hV hVB
      rwa [← sampledPenalty_eq_stagePenalty, ← sampledPenalty_eq_stagePenalty] at h) j

/-- All the finite support defects disappear in the actual selected
limit; their number may grow without bound. -/
theorem selectionDefect_sum_tendsto {target : Set Plane} {U : ℕ → Set Plane}
    (hTarget : IsDownwardCap target) (hU : ∀ n, IsDownwardCap (U n))
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ} (hcoefficient : ∀ n, 0 ≤ coefficient n)
    (hrate : Tendsto coefficient atTop (𝓝 0)) (hHausdorff : CapHausdorffTendsto U target) :
    Tendsto (fun n => ∑ j, selectionDefect target (U n) α (level n) (coefficient n) j)
      atTop (𝓝 0) :=
  supportDefect_sum_tendsto hTarget hU hcoefficient hrate (fun n => stageWeight_nonneg α (level n))
    (fun n => sum_stageWeight_le_one α (level n)) hHausdorff

end PartialGrid

end AmbidextrousSofa
