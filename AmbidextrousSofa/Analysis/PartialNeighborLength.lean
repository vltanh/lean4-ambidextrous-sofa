module

public import AmbidextrousSofa.Analysis.PartialNeighborWalls

@[expose] public section

/-!
# Quantitative proper-history source estimates

The actual finite first and companion sources obey the neighboring-wall
arclength estimates, including the negative self-atom term. The complete
terminal wall only makes the neighboring alternatives stronger.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

namespace PartialGrid

open FinitePolygon AngularGrid

theorem integral_first_source_le_parameters {U : Set Plane} (hU : IsDownwardCap U)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ a b : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ) (hab : a ≤ b)
    (hminus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) + δ) :
    (∫ x in a..b, innerDensity U α hαL grid (scaledSource α grid (Sum.inl t)) x) ≤
      max (support U (companionNormal (scaleAngle α t.val)) - 1 -
        min (companionMinus (support U (unitNormal (scaleAngle α t.val)))
          (support U (companionNormal ((scaleAngle α t.val : ℝ) - δ))) δ)
          (companionPlus (support U (unitNormal (scaleAngle α t.val)))
            (support U (companionNormal ((scaleAngle α t.val : ℝ) + δ))) δ)) 0 +
      max (firstHi (support U (unitNormal (scaleAngle α t.val)))
          (support U (unitNormal ((scaleAngle α t.val : ℝ) - δ))) δ -
        firstLo (support U (unitNormal (scaleAngle α t.val)))
          (support U (unitNormal ((scaleAngle α t.val : ℝ) + δ))) δ) 0 := by
  classical
  have ht : 0 < Real.sin (scaleAngle α t.val) := normal_snd_pos α grid (scaledSource α grid (Sum.inl t))
  have hint := integral_sourceDensity_outward (barrierExpr (pairList α grid) (some (terminalIndex α hαL grid)))
    (normal α grid) (barrierIntercept (normal α grid) (fun i => support U (normal α grid i)))
    (scaledSource α grid (Sum.inl t)) hab
  change (∫ x in a..b, innerDensity U α hαL grid (scaledSource α grid (Sum.inl t)) x) =
    volume.real (Ioc a b ∩ innerSourceSet U α hαL grid (scaledSource α grid (Sum.inl t))) / Real.sin (scaleAngle α t.val) at hint
  rw [hint]
  apply measure_parameterIntervals_le ht
    ((support U (unitNormal (scaleAngle α t.val)) - 1) * Real.cos (scaleAngle α t.val))
  intro x hx
  exact first_source_neighbor_parameters hU α hαL grid t hc hs hminus hplus hx.2

/-- The refined first-wall source estimate for the actual finite niche,
on any ordered spatial integration interval. -/
theorem integral_first_source_le {U : Set Plane} (hU : IsDownwardCap U)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ a b : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ)
    (hh : Real.cos (δ / 2) ≠ 0) (hab : a ≤ b)
    (hminus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) + δ) :
    (∫ x in a..b, innerDensity U α hαL grid (scaledSource α grid (Sum.inl t)) x) ≤
      Real.tan δ * (|firstCornerSecant U (scaleAngle α t.val) δ| + Real.tan (δ / 2)) +
        max (2 * Real.tan (δ / 2) - (upperCurvature U {((scaleAngle α t.val : QuarterAngle) : ℝ)}).toReal) 0 := by
  have hraw := integral_first_source_le_parameters hU α hαL grid t hc hs hab hminus hplus
  have hcomp := companion_interval_length_le hc hs hh
    (hU.companion_secondDifference_nonneg (scaleAngle α t.val) hs.le)
  have hfirst := first_interval_length_le_curvature hU (scaleAngle α t.val) hs hh
  exact hraw.trans (add_le_add hcomp (max_le_max hfirst le_rfl))

theorem integral_second_source_le_parameters {U : Set Plane} (hU : IsDownwardCap U)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ a b : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ) (hab : a ≤ b)
    (hminus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) + δ) :
    (∫ x in a..b, innerDensity U α hαL grid (scaledSource α grid (Sum.inr t)) x) ≤
      max (support U (unitNormal (scaleAngle α t.val)) - 1 -
        min (companionMinus (support U (companionNormal (scaleAngle α t.val)))
          (support U (unitNormal ((scaleAngle α t.val : ℝ) + δ))) δ)
          (companionPlus (support U (companionNormal (scaleAngle α t.val)))
            (support U (unitNormal ((scaleAngle α t.val : ℝ) - δ))) δ)) 0 +
      max (firstHi (support U (companionNormal (scaleAngle α t.val)))
          (support U (companionNormal ((scaleAngle α t.val : ℝ) + δ))) δ -
        firstLo (support U (companionNormal (scaleAngle α t.val)))
          (support U (companionNormal ((scaleAngle α t.val : ℝ) - δ))) δ) 0 := by
  classical
  have ht : 0 < Real.cos (scaleAngle α t.val) := normal_snd_pos α grid (scaledSource α grid (Sum.inr t))
  have hint := integral_sourceDensity_outward (barrierExpr (pairList α grid) (some (terminalIndex α hαL grid)))
    (normal α grid) (barrierIntercept (normal α grid) (fun i => support U (normal α grid i)))
    (scaledSource α grid (Sum.inr t)) hab
  change (∫ x in a..b, innerDensity U α hαL grid (scaledSource α grid (Sum.inr t)) x) =
    volume.real (Ioc a b ∩ innerSourceSet U α hαL grid (scaledSource α grid (Sum.inr t))) / Real.cos (scaleAngle α t.val) at hint
  rw [hint]
  apply measure_addParameterIntervals_le ht
    (-(support U (companionNormal (scaleAngle α t.val)) - 1) * Real.sin (scaleAngle α t.val))
  intro x hx
  exact second_source_neighbor_parameters hU α hαL grid t hc hs hminus hplus hx.2

theorem integral_second_source_le {U : Set Plane} (hU : IsDownwardCap U)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ a b : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ)
    (hh : Real.cos (δ / 2) ≠ 0) (hab : a ≤ b)
    (hminus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) + δ) :
    (∫ x in a..b, innerDensity U α hαL grid (scaledSource α grid (Sum.inr t)) x) ≤
      Real.tan δ * (|secondCornerSecant U (scaleAngle α t.val) δ| + Real.tan (δ / 2)) +
        max (2 * Real.tan (δ / 2) - (upperCurvature U {(scaleAngle α t.val) + Real.pi / 2}).toReal) 0 := by
  have hraw := integral_second_source_le_parameters hU α hαL grid t hc hs hab hminus hplus
  have hconv : 0 ≤ support U (unitNormal ((scaleAngle α t.val : ℝ) + δ)) +
      support U (unitNormal ((scaleAngle α t.val : ℝ) - δ)) -
        2 * Real.cos δ * support U (unitNormal (scaleAngle α t.val)) := by
    nlinarith [hU.support_secondDifference_nonneg (scaleAngle α t.val) hs.le]
  have hcomp := companion_interval_length_le hc hs hh hconv
  have hfirst := companion_interval_length_le_curvature hU (scaleAngle α t.val) hs hh
  exact hraw.trans (add_le_add hcomp (max_le_max hfirst le_rfl))

end PartialGrid

end AmbidextrousSofa
