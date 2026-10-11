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
          (support U (unitNormal ((scaleAngle α t.val : ℝ) + δ))) δ) 0 :=
  (integral_sourceDensity_outward _ _ _ _ hab).trans_le <|
    measure_parameterIntervals_le (normal_snd_pos α grid _) _ _ _ _ _ fun _ hx =>
      first_source_neighbor_parameters hU α hαL grid t hc hs hminus hplus hx.2

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
        max (2 * Real.tan (δ / 2) - (upperCurvature U {((scaleAngle α t.val : QuarterAngle) : ℝ)}).toReal) 0 :=
  (integral_first_source_le_parameters hU α hαL grid t hc hs hab hminus hplus).trans
    (add_le_add (companion_interval_length_le hc hs hh
      (hU.companion_secondDifference_nonneg _ hs.le))
      (max_le_max (first_interval_length_le_curvature hU _ hs hh) le_rfl))

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
          (support U (companionNormal ((scaleAngle α t.val : ℝ) - δ))) δ) 0 :=
  (integral_sourceDensity_outward _ _ _ _ hab).trans_le <|
    measure_addParameterIntervals_le (normal_snd_pos α grid _) _ _ _ _ _ fun _ hx =>
      second_source_neighbor_parameters hU α hαL grid t hc hs hminus hplus hx.2

theorem integral_second_source_le {U : Set Plane} (hU : IsDownwardCap U)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ a b : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ)
    (hh : Real.cos (δ / 2) ≠ 0) (hab : a ≤ b)
    (hminus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) + δ) :
    (∫ x in a..b, innerDensity U α hαL grid (scaledSource α grid (Sum.inr t)) x) ≤
      Real.tan δ * (|secondCornerSecant U (scaleAngle α t.val) δ| + Real.tan (δ / 2)) +
        max (2 * Real.tan (δ / 2) - (upperCurvature U {(scaleAngle α t.val) + Real.pi / 2}).toReal) 0 :=
  (integral_second_source_le_parameters hU α hαL grid t hc hs hab hminus hplus).trans
    (add_le_add (companion_interval_length_le hc hs hh
      (by linarith [hU.support_secondDifference_nonneg (scaleAngle α t.val) hs.le]))
      (max_le_max (companion_interval_length_le_curvature hU _ hs hh) le_rfl))

end PartialGrid

end AmbidextrousSofa
