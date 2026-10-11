module

public import AmbidextrousSofa.Analysis.PartialSelectedCurvature
public import AmbidextrousSofa.Analysis.NeighborCompanion

@[expose] public section

/-!
# Actual proper-history sources and their neighboring walls

Every nonterminal source comes from one of the sampled visited corners.
The same two neighboring-wall alternatives constrain its tangent
parameter. The rescaled endpoint at the terminal angle is allowed in
those alternatives because the complete terminal first wall dominates
the terminal corner.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace PartialGrid

open FinitePolygon AngularGrid

def scaledSource (α : TerminalAngle) (grid : Finset QuarterAngle) :
    AngularGrid.SourceIndex grid → SourceIndex α grid
  | Sum.inl t => Sum.inl (scaledInterior α grid t)
  | Sum.inr t => Sum.inr (scaledInterior α grid t)

theorem scaledSource_ne_terminal (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    (grid : Finset QuarterAngle) : ∀ j, scaledSource α grid j ≠ terminalIndex α hαL grid
  | Sum.inl t, h => (scaleAngle_mem_open α (interiorPoint_mem grid t)).2.ne
      (congrArg (fun s : InteriorPoint (outerGrid α grid) => (s.val : ℝ)) (Sum.inl.inj h))
  | Sum.inr _, h => Sum.inr_ne_inl h

def innerSourceSet (U : Set Plane) (α : TerminalAngle)
    (hαL : (α : ℝ) < Real.pi / 2) (grid : Finset QuarterAngle)
    (j : SourceIndex α grid) : Set ℝ :=
  (barrierExpr (pairList α grid) (some (terminalIndex α hαL grid))).sourceSet
    (wallSlope (normal α grid))
    (barrierIntercept (normal α grid) (fun i => support U (normal α grid i))) (some j)

theorem innerSource_height (U : Set Plane) (α : TerminalAngle)
    (hαL : (α : ℝ) < Real.pi / 2) (grid : Finset QuarterAngle)
    (j : SourceIndex α grid) {x : ℝ} (hx : x ∈ innerSourceSet U α hαL grid j) :
    finiteBarrier U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)) x =
      supportWall U (normal α grid j) x := by
  rw [finiteBarrier_eq_eval (normal α grid) _ (fun _ => rfl), WallExpr.eval_eq_source,
    show _ = some j from hx, ← supportWall_eq_affine]

/-- A nonterminal source is the lower wall of one of the sampled corners. -/
theorem innerSource_corner (U : Set Plane) (α : TerminalAngle)
    (hαL : (α : ℝ) < Real.pi / 2) (grid : Finset QuarterAngle)
    {j : SourceIndex α grid} (hj : j ≠ terminalIndex α hαL grid)
    {x : ℝ} (hx : x ∈ innerSourceSet U α hαL grid j) :
    ∃ s : InteriorPoint grid,
      (j = Sum.inl (scaledInterior α grid s) ∧
        supportWall U (normal α grid (Sum.inl (scaledInterior α grid s))) x ≤
          supportWall U (normal α grid (Sum.inr (scaledInterior α grid s))) x) ∨
      (j = Sum.inr (scaledInterior α grid s) ∧
        supportWall U (normal α grid (Sum.inr (scaledInterior α grid s))) x ≤
          supportWall U (normal α grid (Sum.inl (scaledInterior α grid s))) x) := by
  classical
  change (if _ ≤ _ then some (terminalIndex α hαL grid) else _) = some j at hx
  split_ifs at hx
  · exact absurd (Option.some.inj hx).symm hj
  obtain ⟨_, hij, hsel⟩ := nicheExpr_source_some hx
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hij
  refine ⟨s, (cornerExpr_source_cases _ _).imp (fun h => ⟨Option.some.inj (hsel.symm.trans h.1), ?_⟩)
    (fun h => ⟨Option.some.inj (hsel.symm.trans h.1), ?_⟩)⟩ <;>
    simpa only [← supportWall_eq_affine] using h.2

theorem innerSource_origin (U : Set Plane) (α : TerminalAngle)
    (hαL : (α : ℝ) < Real.pi / 2) (grid : Finset QuarterAngle)
    {j : SourceIndex α grid} (hj : j ≠ terminalIndex α hαL grid)
    {x : ℝ} (hx : x ∈ innerSourceSet U α hαL grid j) :
    ∃ k : AngularGrid.SourceIndex grid, j = scaledSource α grid k := by
  obtain ⟨s, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ := innerSource_corner U α hαL grid hj hx
  exacts [⟨Sum.inl s, rfl⟩, ⟨Sum.inr s, rfl⟩]

theorem first_source_le_companion (U : Set Plane) (α : TerminalAngle)
    (hαL : (α : ℝ) < Real.pi / 2) (grid : Finset QuarterAngle)
    (t : InteriorPoint grid) {x : ℝ}
    (hx : x ∈ innerSourceSet U α hαL grid (scaledSource α grid (Sum.inl t))) :
    supportWall U (unitNormal (scaleAngle α t.val)) x ≤
      supportWall U (companionNormal (scaleAngle α t.val)) x := by
  obtain ⟨s, ⟨h, hle⟩ | ⟨h, -⟩⟩ :=
    innerSource_corner U α hαL grid (scaledSource_ne_terminal α hαL grid _) hx
  · rwa [← Sum.inl.inj h] at hle
  · exact (Sum.inl_ne_inr h).elim

theorem second_source_le_first (U : Set Plane) (α : TerminalAngle)
    (hαL : (α : ℝ) < Real.pi / 2) (grid : Finset QuarterAngle)
    (t : InteriorPoint grid) {x : ℝ}
    (hx : x ∈ innerSourceSet U α hαL grid (scaledSource α grid (Sum.inr t))) :
    supportWall U (companionNormal (scaleAngle α t.val)) x ≤
      supportWall U (unitNormal (scaleAngle α t.val)) x := by
  obtain ⟨s, ⟨h, -⟩ | ⟨h, hle⟩⟩ :=
    innerSource_corner U α hαL grid (scaledSource_ne_terminal α hαL grid _) hx
  · exact (Sum.inr_ne_inl h).elim
  · rwa [← Sum.inr.inj h] at hle

theorem above_barrier_wall_alternative {U : Set Plane} (hU : IsDownwardCap U)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2) (grid : Finset QuarterAngle)
    {p : Plane} (hp0 : 0 ≤ p.2)
    (hpB : finiteBarrier U (normal α grid) (pairList α grid)
      (some (terminalIndex α hαL grid)) p.1 ≤ p.2)
    {s : QuarterAngle} (hs : s ∈ grid) :
    support U (unitNormal (scaleAngle α s)) - 1 ≤ coordDot p (unitNormal (scaleAngle α s)) ∨
      support U (companionNormal (scaleAngle α s)) - 1 ≤
        coordDot p (companionNormal (scaleAngle α s)) := by
  have hπ := Real.pi_pos
  by_cases hs0 : (s : ℝ) = 0
  · right
    simp [show (scaleAngle α s : ℝ) = 0 by simp [scaleAngle, unitParameter, hs0], companionNormal,
      coordDot]
    linarith [hU.support_upward_le_one]
  have hspos : 0 < (scaleAngle α s : ℝ) :=
    mul_pos (TerminalAngle.pos α) (div_pos (s.property.1.lt_of_ne' hs0) (by linarith))
  have hsL := (scaleAngle_le_terminal α s).trans_lt hαL
  rw [finiteBarrier_eq_barrier] at hpB
  refine (min_le_iff.mp (((le_max_left _ _).trans (clip_le_niche U α grid p.1 hs)).trans
    ((le_max_left _ _).trans hpB))).imp (fun h => ?_) (fun h => ?_)
  · rw [← supportWall_unitNormal] at h
    exact (supportWall_le_iff (Real.sin_pos_of_pos_of_lt_pi hspos (by linarith)) p.1 p.2).mp h
  · rw [← supportWall_companionNormal] at h
    exact (supportWall_le_iff (Real.cos_pos_of_mem_Ioo ⟨by linarith, hsL⟩) p.1 p.2).mp h

theorem first_source_neighbor_parameters {U : Set Plane} (hU : IsDownwardCap U)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ)
    (hminus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) + δ)
    {x : ℝ} (hx : x ∈ innerSourceSet U α hαL grid (scaledSource α grid (Sum.inl t))) :
    ∃ v : ℝ, x = (support U (unitNormal (scaleAngle α t.val)) - 1) * Real.cos (scaleAngle α t.val) - v * Real.sin (scaleAngle α t.val) ∧
      v ∈ neighborParameters (support U (unitNormal (scaleAngle α t.val))) (support U (companionNormal (scaleAngle α t.val)))
        (support U (unitNormal ((scaleAngle α t.val : ℝ) - δ))) (support U (unitNormal ((scaleAngle α t.val : ℝ) + δ)))
        (support U (companionNormal ((scaleAngle α t.val : ℝ) - δ)))
        (support U (companionNormal ((scaleAngle α t.val : ℝ) + δ))) δ := by
  let y := supportWall U (unitNormal (scaleAngle α t.val)) x
  let v := coordDot (x, y) (companionNormal (scaleAngle α t.val))
  have hy := innerSource_height U α hαL grid _ hx
  have hy0 : 0 ≤ y := (finiteBarrier_nonneg _ _ _ _ _).trans_eq hy
  have hn := normal_snd_pos α grid (scaledSource α grid (Sum.inl t))
  have hp : ((x, y) : Plane) = wallPoint U (scaleAngle α t.val) v := point_eq_wallPoint
    (((le_supportWall_iff hn x y).mp le_rfl).antisymm ((supportWall_le_iff hn x y).mp le_rfl))
  obtain ⟨sm, hsm, hsmval⟩ := hminus
  obtain ⟨sp, hsp, hspval⟩ := hplus
  have hm := above_barrier_wall_alternative hU α hαL grid (p := (x, y)) hy0 hy.le hsm
  have hp' := above_barrier_wall_alternative hU α hαL grid (p := (x, y)) hy0 hy.le hsp
  simp only [hsmval, hspval, hp, dot_wallPoint_first, dot_wallPoint_companion, sub_sub_cancel_left,
    sub_sub_cancel, add_sub_cancel_left, sub_add_cancel_left, Real.cos_neg, Real.sin_neg] at hm hp'
  refine ⟨v, by simpa only [wallPoint_fst] using congrArg Prod.fst hp, mem_neighborParameters hc hs
    ((le_supportWall_iff (normal_snd_pos α grid (scaledSource α grid (Sum.inr t))) x y).mp
      (first_source_le_companion U α hαL grid t hx)) (hm.imp_left fun h => by linarith)
    (hp'.imp_right fun h => by linarith)⟩

theorem second_source_neighbor_parameters {U : Set Plane} (hU : IsDownwardCap U)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ)
    (hminus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) + δ)
    {x : ℝ} (hx : x ∈ innerSourceSet U α hαL grid (scaledSource α grid (Sum.inr t))) :
    ∃ v : ℝ, x = -(support U (companionNormal (scaleAngle α t.val)) - 1) * Real.sin (scaleAngle α t.val) +
        v * Real.cos (scaleAngle α t.val) ∧
      v ∈ neighborParameters (support U (companionNormal (scaleAngle α t.val))) (support U (unitNormal (scaleAngle α t.val)))
        (support U (companionNormal ((scaleAngle α t.val : ℝ) + δ)))
        (support U (companionNormal ((scaleAngle α t.val : ℝ) - δ)))
        (support U (unitNormal ((scaleAngle α t.val : ℝ) + δ)))
        (support U (unitNormal ((scaleAngle α t.val : ℝ) - δ))) δ := by
  let y := supportWall U (companionNormal (scaleAngle α t.val)) x
  let v := coordDot (x, y) (unitNormal (scaleAngle α t.val))
  have hy := innerSource_height U α hαL grid _ hx
  have hy0 : 0 ≤ y := (finiteBarrier_nonneg _ _ _ _ _).trans_eq hy
  have hn := normal_snd_pos α grid (scaledSource α grid (Sum.inr t))
  have hp : ((x, y) : Plane) = companionPoint U (scaleAngle α t.val) v := point_eq_companionPoint
    (((le_supportWall_iff hn x y).mp le_rfl).antisymm ((supportWall_le_iff hn x y).mp le_rfl))
  obtain ⟨sm, hsm, hsmval⟩ := hminus
  obtain ⟨sp, hsp, hspval⟩ := hplus
  have hm := above_barrier_wall_alternative hU α hαL grid (p := (x, y)) hy0 hy.le hsm
  have hp' := above_barrier_wall_alternative hU α hαL grid (p := (x, y)) hy0 hy.le hsp
  simp only [hsmval, hspval, hp, dot_companionPoint_first, dot_companionPoint_companion, sub_sub_cancel_left,
    sub_sub_cancel, add_sub_cancel_left, sub_add_cancel_left, Real.cos_neg, Real.sin_neg] at hm hp'
  refine ⟨v, by simpa only [companionPoint_fst] using congrArg Prod.fst hp,
    mem_neighborParameters hc hs
      ((le_supportWall_iff (normal_snd_pos α grid (scaledSource α grid (Sum.inl t))) x y).mp
        (second_source_le_first U α hαL grid t hx))
      (hp'.symm.imp (fun h => by linarith) fun h => by linarith)
      (hm.symm.imp (fun h => by linarith) fun h => by linarith)⟩

end PartialGrid

end AmbidextrousSofa
