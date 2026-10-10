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
        (support U (companionNormal ((scaleAngle α t.val : ℝ) + δ))) δ := by
  let y := supportWall U (unitNormal (scaleAngle α t.val)) x
  let p : Plane := (x, y)
  let v := coordDot p (companionNormal (scaleAngle α t.val))
  have hy : finiteBarrier U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)) x = y :=
    innerSource_height U α hαL grid (scaledSource α grid (Sum.inl t)) hx
  have hy0 : 0 ≤ p.2 := by
    change 0 ≤ y
    rw [← hy]
    exact finiteBarrier_nonneg _ _ _ _ _
  have hline : coordDot p (unitNormal (scaleAngle α t.val)) =
      support U (unitNormal (scaleAngle α t.val)) - 1 := by
    apply le_antisymm
    · exact (le_supportWall_iff (normal_snd_pos α grid (scaledSource α grid (Sum.inl t))) x y).mp le_rfl
    · exact (supportWall_le_iff (normal_snd_pos α grid (scaledSource α grid (Sum.inl t))) x y).mp le_rfl
  have hp : p = wallPoint U (scaleAngle α t.val) v := point_eq_wallPoint hline
  have hv : v ≤ support U (companionNormal (scaleAngle α t.val)) - 1 :=
    (le_supportWall_iff (normal_snd_pos α grid (scaledSource α grid (Sum.inr t))) x y).mp
      (first_source_le_companion U α hαL grid t hx)
  obtain ⟨sm, hsm, hsmval⟩ := hminus
  obtain ⟨sp, hsp, hspval⟩ := hplus
  have hm := above_barrier_wall_alternative hU α hαL grid hy0 hy.le hsm
  have hp' := above_barrier_wall_alternative hU α hαL grid hy0 hy.le hsp
  rw [hsmval, hp, dot_wallPoint_first, dot_wallPoint_companion,
    show (scaleAngle α t.val : ℝ) - δ - (scaleAngle α t.val : ℝ) = -δ by ring,
    show (scaleAngle α t.val : ℝ) - ((scaleAngle α t.val : ℝ) - δ) = δ by ring,
    Real.cos_neg, Real.sin_neg] at hm
  rw [hspval, hp, dot_wallPoint_first, dot_wallPoint_companion,
    show (scaleAngle α t.val : ℝ) + δ - (scaleAngle α t.val : ℝ) = δ by ring,
    show (scaleAngle α t.val : ℝ) - ((scaleAngle α t.val : ℝ) + δ) = -δ by ring,
    Real.sin_neg, Real.cos_neg] at hp'
  refine ⟨v, ?_, hv, ?_, ?_⟩
  · have h := congrArg Prod.fst hp
    simpa only [p, wallPoint_fst] using h
  · rcases hm with h | h
    · exact Or.inl (by nlinarith only [h])
    · exact Or.inr (by nlinarith only [h])
  · rcases hp' with h | h
    · exact Or.inl (by nlinarith only [h])
    · exact Or.inr (by nlinarith only [h])

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
        (support U (unitNormal ((scaleAngle α t.val : ℝ) - δ))) δ := by
  let y := supportWall U (companionNormal (scaleAngle α t.val)) x
  let p : Plane := (x, y)
  let v := coordDot p (unitNormal (scaleAngle α t.val))
  have hy : finiteBarrier U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)) x = y :=
    innerSource_height U α hαL grid (scaledSource α grid (Sum.inr t)) hx
  have hy0 : 0 ≤ p.2 := by
    change 0 ≤ y
    rw [← hy]
    exact finiteBarrier_nonneg _ _ _ _ _
  have hline : coordDot p (companionNormal (scaleAngle α t.val)) =
      support U (companionNormal (scaleAngle α t.val)) - 1 := by
    apply le_antisymm
    · exact (le_supportWall_iff (normal_snd_pos α grid (scaledSource α grid (Sum.inr t))) x y).mp le_rfl
    · exact (supportWall_le_iff (normal_snd_pos α grid (scaledSource α grid (Sum.inr t))) x y).mp le_rfl
  have hp : p = companionPoint U (scaleAngle α t.val) v := point_eq_companionPoint hline
  have hv : v ≤ support U (unitNormal (scaleAngle α t.val)) - 1 :=
    (le_supportWall_iff (normal_snd_pos α grid (scaledSource α grid (Sum.inl t))) x y).mp
      (second_source_le_first U α hαL grid t hx)
  obtain ⟨sm, hsm, hsmval⟩ := hminus
  obtain ⟨sp, hsp, hspval⟩ := hplus
  have hm := above_barrier_wall_alternative hU α hαL grid hy0 hy.le hsm
  have hp' := above_barrier_wall_alternative hU α hαL grid hy0 hy.le hsp
  rw [hsmval, hp, dot_companionPoint_first, dot_companionPoint_companion,
    show (scaleAngle α t.val : ℝ) - δ - (scaleAngle α t.val : ℝ) = -δ by ring,
    show (scaleAngle α t.val : ℝ) - ((scaleAngle α t.val : ℝ) - δ) = δ by ring,
    Real.cos_neg, Real.sin_neg] at hm
  rw [hspval, hp, dot_companionPoint_first, dot_companionPoint_companion,
    show (scaleAngle α t.val : ℝ) + δ - (scaleAngle α t.val : ℝ) = δ by ring,
    show (scaleAngle α t.val : ℝ) - ((scaleAngle α t.val : ℝ) + δ) = -δ by ring,
    Real.sin_neg, Real.cos_neg] at hp'
  refine ⟨v, ?_, hv, ?_, ?_⟩
  · have h := congrArg Prod.fst hp
    simpa only [p, companionPoint_fst] using h
  · rcases hp' with h | h
    · exact Or.inr (by nlinarith only [h])
    · exact Or.inl (by nlinarith only [h])
  · rcases hm with h | h
    · exact Or.inr (by nlinarith only [h])
    · exact Or.inl (by nlinarith only [h])

theorem innerDensity_eq_zero_of_source_empty (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex α grid) (hempty : innerSourceSet U α hαL grid j = ∅) :
    innerDensity U α hαL grid j = fun _ => 0 := by
  classical
  funext x
  have hnot : x ∉ innerSourceSet U α hαL grid j := by rw [hempty]; exact notMem_empty x
  unfold innerDensity
  rw [outwardVelocity_eq_single, WallExpr.sourceDensity_single]
  exact indicator_of_notMem hnot _

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
    innerSourceSet U α hαL grid (scaledSource α grid (Sum.inl t)) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨v, _, hv⟩ := first_source_neighbor_feasible hU grid t hminus hplus hx
  rw [neighborFeasible_eq_empty_of_forward_separation hc hs hfirst hcompanion] at hv
  exact notMem_empty v hv

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
    innerSourceSet U α hαL grid (scaledSource α grid (Sum.inr t)) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨v, _, hv⟩ := second_source_neighbor_feasible hU grid t hminus hplus hx
  rw [neighborFeasible_eq_empty_of_forward_separation hc hs hfirst hcompanion] at hv
  exact notMem_empty v hv

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
  classical
  have ht : 0 < Real.sin (scaleAngle α t.val) :=
    normal_snd_pos α grid (scaledSource α grid (Sum.inl t))
  have hint := integral_sourceDensity_outward
    (barrierExpr (pairList α grid) (some (terminalIndex α hαL grid)))
    (normal α grid) (barrierIntercept (normal α grid) (fun i => support U (normal α grid i)))
    (scaledSource α grid (Sum.inl t)) hab
  change (∫ x in a..b, innerDensity U α hαL grid (scaledSource α grid (Sum.inl t)) x) =
    volume.real (Ioc a b ∩ innerSourceSet U α hαL grid (scaledSource α grid (Sum.inl t))) /
      Real.sin (scaleAngle α t.val) at hint
  rw [hint]
  have hbound := measure_parameterIntervals_le
    (S := Ioc a b ∩ innerSourceSet U α hαL grid (scaledSource α grid (Sum.inl t)))
    ht ((support U (unitNormal (scaleAngle α t.val)) - 1) * Real.cos (scaleAngle α t.val))
    (firstLo (support U (unitNormal (scaleAngle α t.val)))
      (support U (unitNormal ((scaleAngle α t.val : ℝ) + δ))) δ)
    (firstHi (support U (unitNormal (scaleAngle α t.val)))
      (support U (unitNormal ((scaleAngle α t.val : ℝ) - δ))) δ) 0 0 (by
        intro x hx
        obtain ⟨v, hvx, hv⟩ := first_source_neighbor_feasible hU grid t hminus hplus hx.2
        exact ⟨v, hvx, Or.inl (neighborFeasible_subset_self_interval hc hs hsepMinus hsepPlus hv)⟩)
  simp only [sub_self, max_self, add_zero] at hbound
  exact hbound.trans
    (max_le_max (first_interval_length_le_curvature hU (scaleAngle α t.val) hs hh) le_rfl)

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
  classical
  have ht : 0 < Real.cos (scaleAngle α t.val) :=
    normal_snd_pos α grid (scaledSource α grid (Sum.inr t))
  have hint := integral_sourceDensity_outward
    (barrierExpr (pairList α grid) (some (terminalIndex α hαL grid)))
    (normal α grid) (barrierIntercept (normal α grid) (fun i => support U (normal α grid i)))
    (scaledSource α grid (Sum.inr t)) hab
  change (∫ x in a..b, innerDensity U α hαL grid (scaledSource α grid (Sum.inr t)) x) =
    volume.real (Ioc a b ∩ innerSourceSet U α hαL grid (scaledSource α grid (Sum.inr t))) /
      Real.cos (scaleAngle α t.val) at hint
  rw [hint]
  have hbound := measure_addParameterIntervals_le
    (S := Ioc a b ∩ innerSourceSet U α hαL grid (scaledSource α grid (Sum.inr t))) ht
    (-(support U (companionNormal (scaleAngle α t.val)) - 1) * Real.sin (scaleAngle α t.val))
    (firstLo (support U (companionNormal (scaleAngle α t.val)))
      (support U (companionNormal ((scaleAngle α t.val : ℝ) - δ))) δ)
    (firstHi (support U (companionNormal (scaleAngle α t.val)))
      (support U (companionNormal ((scaleAngle α t.val : ℝ) + δ))) δ) 0 0 (by
        intro x hx
        obtain ⟨v, hvx, hv⟩ := second_source_neighbor_feasible hU grid t hminus hplus hx.2
        exact ⟨v, hvx, Or.inl (neighborFeasible_subset_self_interval hc hs hsepPlus hsepMinus hv)⟩)
  simp only [sub_self, max_self, add_zero] at hbound
  exact hbound.trans
    (max_le_max (companion_interval_length_le_curvature hU (scaleAngle α t.val) hs hh) le_rfl)

theorem IsSelectedPolygon.curvature_atom_le_error_of_source_empty {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U) (hc : 0 ≤ coefficient)
    (j : SourceIndex α (dyadic level))
    (hempty : innerSourceSet U α hαL (dyadic level) j = ∅) :
    (upperCurvature U {fullAngle α (dyadic level) j}).toReal ≤
      middleOuterMass U α (dyadic level) j + selectionDefect target U α level coefficient j := by
  have h := hU.curvature_atom_le hc j
  rw [innerDensity_eq_zero_of_source_empty U (dyadic level) j hempty,
    intervalIntegral.integral_zero, zero_add] at h
  exact h

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
  change innerSourceMass U α hαL (dyadic level) j ≤
    max (2 * d - (upperCurvature U {fullAngle α (dyadic level) j}).toReal) 0 at hsource
  have herror := add_nonneg (middleOuterMass_nonneg hU.isCap α (dyadic level) j)
    (selectionDefect_nonneg target U α level hc j)
  have hbound : (upperCurvature U {fullAngle α (dyadic level) j}).toReal ≤
      0 + max (2 * d - (upperCurvature U {fullAngle α (dyadic level) j}).toReal) 0 +
        (middleOuterMass U α (dyadic level) j + selectionDefect target U α level coefficient j) := by
    linarith only [hatom, hsource]
  have h := solve_curvature_self_bound herror hbound
  have heq : ((0 : ℝ) + 2 * d) / 2 = d := by ring
  simpa only [heq, max_eq_right hd, add_assoc] using h

end PartialGrid
end AmbidextrousSofa
