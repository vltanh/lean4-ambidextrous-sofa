module

public import AmbidextrousSofa.Analysis.PartialSourceMass
public import AmbidextrousSofa.Analysis.ShadowSecants

@[expose] public section

/-!
# Strict neighboring-wall shadowing in the actual proper graph

The original pair of neighboring corridor alternatives is retained.
The whole terminal wall strengthens these alternatives, including when
the upper neighbor is the terminal sample. A selected source can thus
be empty or confined to its own wall interval, with its actual curvature
atom subtracted from that interval's length.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa
namespace PartialGrid

open FinitePolygon AngularGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

theorem first_source_neighbor_feasible {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ : ℝ}
    (hminus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) + δ)
    {x : ℝ} (hx : x ∈ innerSourceSet U α hαL grid (scaledSource α grid (Sum.inl t))) :
    ∃ v : ℝ, x = (support U (unitNormal (scaleAngle α t.val)) - 1) *
        Real.cos (scaleAngle α t.val) - v * Real.sin (scaleAngle α t.val) ∧
      v ∈ neighborFeasible (support U (unitNormal (scaleAngle α t.val)))
        (support U (companionNormal (scaleAngle α t.val)))
        (support U (unitNormal ((scaleAngle α t.val : ℝ) - δ)))
        (support U (unitNormal ((scaleAngle α t.val : ℝ) + δ)))
        (support U (companionNormal ((scaleAngle α t.val : ℝ) - δ)))
        (support U (companionNormal ((scaleAngle α t.val : ℝ) + δ))) δ :=
  first_source_wall_constraints hU α hαL grid t hminus hplus hx

theorem second_source_neighbor_feasible {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ : ℝ}
    (hminus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) + δ)
    {x : ℝ} (hx : x ∈ innerSourceSet U α hαL grid (scaledSource α grid (Sum.inr t))) :
    ∃ v : ℝ, x = -(support U (companionNormal (scaleAngle α t.val)) - 1) *
        Real.sin (scaleAngle α t.val) + v * Real.cos (scaleAngle α t.val) ∧
      v ∈ neighborFeasible (support U (companionNormal (scaleAngle α t.val)))
        (support U (unitNormal (scaleAngle α t.val)))
        (support U (companionNormal ((scaleAngle α t.val : ℝ) + δ)))
        (support U (companionNormal ((scaleAngle α t.val : ℝ) - δ)))
        (support U (unitNormal ((scaleAngle α t.val : ℝ) + δ)))
        (support U (unitNormal ((scaleAngle α t.val : ℝ) - δ))) δ :=
  second_source_wall_constraints hU α hαL grid t hminus hplus hx

theorem innerDensity_eq_zero_of_source_empty (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex α grid) (hempty : innerSourceSet U α hαL grid j = ∅) :
    innerDensity U α hαL grid j = fun _ => 0 := by
  classical
  funext x
  rw [innerDensity, outwardVelocity_eq_single, WallExpr.sourceDensity_single]
  exact indicator_of_notMem (hempty ▸ notMem_empty x : x ∉ innerSourceSet U α hαL grid j) _

theorem first_source_empty_of_forward_separation {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ)
    (hminus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) + δ)
    (hfirst : support U (companionNormal (scaleAngle α t.val)) - 1 <
      firstLo (support U (unitNormal (scaleAngle α t.val)))
        (support U (unitNormal ((scaleAngle α t.val : ℝ) + δ))) δ)
    (hcompanion : support U (companionNormal (scaleAngle α t.val)) - 1 <
      companionPlus (support U (unitNormal (scaleAngle α t.val)))
        (support U (companionNormal ((scaleAngle α t.val : ℝ) + δ))) δ) :
    innerSourceSet U α hαL grid (scaledSource α grid (Sum.inl t)) = ∅ :=
  eq_empty_of_forall_notMem fun x hx => by
    obtain ⟨v, -, hv⟩ := first_source_neighbor_feasible hU grid t hminus hplus hx
    exact (neighborFeasible_eq_empty_of_forward_separation hc hs hfirst hcompanion).subset hv

theorem second_source_empty_of_backward_separation {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ)
    (hminus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) + δ)
    (hfirst : support U (unitNormal (scaleAngle α t.val)) - 1 <
      firstLo (support U (companionNormal (scaleAngle α t.val)))
        (support U (companionNormal ((scaleAngle α t.val : ℝ) - δ))) δ)
    (hcompanion : support U (unitNormal (scaleAngle α t.val)) - 1 <
      companionPlus (support U (companionNormal (scaleAngle α t.val)))
        (support U (unitNormal ((scaleAngle α t.val : ℝ) - δ))) δ) :
    innerSourceSet U α hαL grid (scaledSource α grid (Sum.inr t)) = ∅ :=
  eq_empty_of_forall_notMem fun x hx => by
    obtain ⟨v, -, hv⟩ := second_source_neighbor_feasible hU grid t hminus hplus hx
    exact (neighborFeasible_eq_empty_of_forward_separation hc hs hfirst hcompanion).subset hv

theorem integral_first_source_le_self_interval {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ a b : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ)
    (hh : Real.cos (δ / 2) ≠ 0) (hab : a ≤ b)
    (hminus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) + δ)
    (hsepMinus : support U (companionNormal (scaleAngle α t.val)) - 1 <
      companionMinus (support U (unitNormal (scaleAngle α t.val)))
        (support U (companionNormal ((scaleAngle α t.val : ℝ) - δ))) δ)
    (hsepPlus : firstHi (support U (unitNormal (scaleAngle α t.val)))
        (support U (unitNormal ((scaleAngle α t.val : ℝ) - δ))) δ <
      companionPlus (support U (unitNormal (scaleAngle α t.val)))
        (support U (companionNormal ((scaleAngle α t.val : ℝ) + δ))) δ) :
    (∫ x in a..b, innerDensity U α hαL grid (scaledSource α grid (Sum.inl t)) x) ≤
      max (2 * Real.tan (δ / 2) - (upperCurvature U {((scaleAngle α t.val : QuarterAngle) : ℝ)}).toReal) 0 := by
  have := measure_parameterIntervals_le (normal_snd_pos α grid (scaledSource α grid (Sum.inl t)))
    _ _ _ 0 0 fun x (hx : x ∈ Ioc a b ∩ innerSourceSet U α hαL grid _) => by
      obtain ⟨v, hvx, hv⟩ := first_source_neighbor_feasible hU grid t hminus hplus hx.2
      exact ⟨v, hvx, .inl (neighborFeasible_subset_self_interval hc hs hsepMinus hsepPlus hv)⟩
  simp only [sub_self, max_self, add_zero] at this
  exact (integral_sourceDensity_outward _ _ _ _ hab).trans_le
    (this.trans (max_le_max (first_interval_length_le_curvature hU _ hs hh) le_rfl))

theorem integral_second_source_le_self_interval {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ a b : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ)
    (hh : Real.cos (δ / 2) ≠ 0) (hab : a ≤ b)
    (hminus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) + δ)
    (hsepPlus : support U (unitNormal (scaleAngle α t.val)) - 1 <
      companionMinus (support U (companionNormal (scaleAngle α t.val)))
        (support U (unitNormal ((scaleAngle α t.val : ℝ) + δ))) δ)
    (hsepMinus : firstHi (support U (companionNormal (scaleAngle α t.val)))
        (support U (companionNormal ((scaleAngle α t.val : ℝ) + δ))) δ <
      companionPlus (support U (companionNormal (scaleAngle α t.val)))
        (support U (unitNormal ((scaleAngle α t.val : ℝ) - δ))) δ) :
    (∫ x in a..b, innerDensity U α hαL grid (scaledSource α grid (Sum.inr t)) x) ≤
      max (2 * Real.tan (δ / 2) -
        (upperCurvature U {(scaleAngle α t.val : ℝ) + Real.pi / 2}).toReal) 0 := by
  have := measure_addParameterIntervals_le
    (normal_snd_pos α grid (scaledSource α grid (Sum.inr t))) _ _ _ 0 0
    fun x (hx : x ∈ Ioc a b ∩ innerSourceSet U α hαL grid _) => by
      obtain ⟨v, hvx, hv⟩ := second_source_neighbor_feasible hU grid t hminus hplus hx.2
      exact ⟨v, hvx, .inl (neighborFeasible_subset_self_interval hc hs hsepPlus hsepMinus hv)⟩
  simp only [sub_self, max_self, add_zero] at this
  exact (integral_sourceDensity_outward _ _ _ _ hab).trans_le
    (this.trans (max_le_max (companion_interval_length_le_curvature hU _ hs hh) le_rfl))

theorem IsSelectedPolygon.curvature_atom_le_error_of_source_empty {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U) (hc : 0 ≤ coefficient)
    (j : SourceIndex α (dyadic level))
    (hempty : innerSourceSet U α hαL (dyadic level) j = ∅) :
    (upperCurvature U {fullAngle α (dyadic level) j}).toReal ≤
      middleOuterMass U α (dyadic level) j + selectionDefect target U α level coefficient j := by
  have h := hU.curvature_atom_le hc j
  rwa [innerDensity_eq_zero_of_source_empty U (dyadic level) j hempty,
    intervalIntegral.integral_zero, zero_add] at h

theorem IsSelectedPolygon.curvature_atom_le_half_of_self_interval {target U : Set Plane}
    {a b coefficient d : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U) (hc : 0 ≤ coefficient)
    (j : SourceIndex α (dyadic level)) (hd : 0 ≤ d)
    (hsource : (∫ x in (horizontalLeft U + capWidth U / 4)..(horizontalRight U - capWidth U / 4),
        innerDensity U α hαL (dyadic level) j x) ≤
      max (2 * d - (upperCurvature U {fullAngle α (dyadic level) j}).toReal) 0) :
    (upperCurvature U {fullAngle α (dyadic level) j}).toReal ≤
      d + middleOuterMass U α (dyadic level) j + selectionDefect target U α level coefficient j := by
  have hatom := hU.curvature_atom_le_mass hc j
  have he := add_nonneg (middleOuterMass_nonneg hU.isCap α (dyadic level) j)
    (selectionDefect_nonneg target U α level hc j)
  rw [innerSourceMass] at hatom
  rcases max_choice (2 * d - (upperCurvature U {fullAngle α (dyadic level) j}).toReal) 0
    with h | h <;> linarith [hsource.trans_eq h]

end PartialGrid
end AmbidextrousSofa
