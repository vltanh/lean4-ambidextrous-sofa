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

theorem scaleAngle_injective (α : TerminalAngle) : Function.Injective (scaleAngle α) := by
  intro s t h
  apply Subtype.ext
  have hreal := congrArg (fun u : QuarterAngle => (u : ℝ)) h
  change (α : ℝ) * ((s : ℝ) / (Real.pi / 2)) =
    (α : ℝ) * ((t : ℝ) / (Real.pi / 2)) at hreal
  have hquot := mul_left_cancel₀ (TerminalAngle.pos α).ne' hreal
  have hprod := congrArg (fun z : ℝ => z * (Real.pi / 2)) hquot
  simpa only [div_mul_cancel₀ _ (by linarith [Real.pi_pos] : Real.pi / 2 ≠ 0)] using hprod

theorem scaledInterior_injective (α : TerminalAngle) (grid : Finset QuarterAngle) :
    Function.Injective (scaledInterior α grid) := by
  intro s t h
  apply Subtype.ext
  exact scaleAngle_injective α (congrArg Subtype.val h)

def scaledSource (α : TerminalAngle) (grid : Finset QuarterAngle) :
    AngularGrid.SourceIndex grid → SourceIndex α grid
  | Sum.inl t => Sum.inl (scaledInterior α grid t)
  | Sum.inr t => Sum.inr (scaledInterior α grid t)

theorem scaledSource_ne_terminal (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    (grid : Finset QuarterAngle) (j : AngularGrid.SourceIndex grid) :
    scaledSource α grid j ≠ terminalIndex α hαL grid := by
  cases j with
  | inl t =>
    intro h
    have h' := congrArg (fun s : InteriorPoint (outerGrid α grid) => (s.val : ℝ)) (Sum.inl.inj h)
    change (scaleAngle α t.val : ℝ) = (α : ℝ) at h'
    exact (scaleAngle_mem_open α (interiorPoint_mem grid t)).2.ne h'
  | inr t => simp [scaledSource, terminalIndex]

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
  rw [finiteBarrier_eq_eval (normal α grid) _ (fun _ => rfl), WallExpr.eval_eq_source]
  change (barrierExpr (pairList α grid) (some (terminalIndex α hαL grid))).source
    (fun i => wallSlope (normal α grid) i * x +
      barrierIntercept (normal α grid) (fun k => support U (normal α grid k)) i) = some j at hx
  rw [hx, ← supportWall_eq_affine]

theorem niche_source_of_ne_terminal (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    (grid : Finset QuarterAngle) {v : Option (SourceIndex α grid) → ℝ}
    {j : SourceIndex α grid} (hj : j ≠ terminalIndex α hαL grid)
    (hsource : (barrierExpr (pairList α grid) (some (terminalIndex α hαL grid))).source v = some j) :
    (nicheExpr (pairList α grid)).source v = some j := by
  change (if (nicheExpr (pairList α grid)).eval v ≤ v (some (terminalIndex α hαL grid))
    then some (terminalIndex α hαL grid) else (nicheExpr (pairList α grid)).source v) = some j at hsource
  split_ifs at hsource with hle
  · exact False.elim (hj (Option.some.inj hsource).symm)
  · exact hsource

theorem innerSource_origin (U : Set Plane) (α : TerminalAngle)
    (hαL : (α : ℝ) < Real.pi / 2) (grid : Finset QuarterAngle)
    {j : SourceIndex α grid} (hj : j ≠ terminalIndex α hαL grid)
    {x : ℝ} (hx : x ∈ innerSourceSet U α hαL grid j) :
    ∃ k : AngularGrid.SourceIndex grid, j = scaledSource α grid k := by
  classical
  let v : Option (SourceIndex α grid) → ℝ := fun i => wallSlope (normal α grid) i * x +
    barrierIntercept (normal α grid) (fun k => support U (normal α grid k)) i
  have hsource := niche_source_of_ne_terminal α hαL grid hj (show
    (barrierExpr (pairList α grid) (some (terminalIndex α hαL grid))).source v = some j from hx)
  obtain ⟨ij, hij, hselected⟩ := nicheExpr_source_some hsource
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hij
  rcases cornerExpr_source_cases
      (Sum.inl (scaledInterior α grid s), Sum.inr (scaledInterior α grid s)) v with h | h
  · exact ⟨Sum.inl s, Option.some.inj (hselected.symm.trans h.1)⟩
  · exact ⟨Sum.inr s, Option.some.inj (hselected.symm.trans h.1)⟩

theorem first_source_le_companion (U : Set Plane) (α : TerminalAngle)
    (hαL : (α : ℝ) < Real.pi / 2) (grid : Finset QuarterAngle)
    (t : InteriorPoint grid) {x : ℝ}
    (hx : x ∈ innerSourceSet U α hαL grid (scaledSource α grid (Sum.inl t))) :
    supportWall U (unitNormal (scaleAngle α t.val)) x ≤
      supportWall U (companionNormal (scaleAngle α t.val)) x := by
  classical
  let v : Option (SourceIndex α grid) → ℝ := fun i => wallSlope (normal α grid) i * x +
    barrierIntercept (normal α grid) (fun j => support U (normal α grid j)) i
  have hsource := niche_source_of_ne_terminal α hαL grid
    (scaledSource_ne_terminal α hαL grid (Sum.inl t)) (show
      (barrierExpr (pairList α grid) (some (terminalIndex α hαL grid))).source v =
        some (scaledSource α grid (Sum.inl t)) from hx)
  obtain ⟨ij, hij, hselected⟩ := nicheExpr_source_some hsource
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hij
  rcases cornerExpr_source_cases
      (Sum.inl (scaledInterior α grid s), Sum.inr (scaledInterior α grid s)) v with h | h
  · have heq : t = s := scaledInterior_injective α grid
      (Sum.inl.inj (Option.some.inj (hselected.symm.trans h.1)))
    subst s
    have h2 : supportWall U (normal α grid (Sum.inl (scaledInterior α grid t))) x ≤
        supportWall U (normal α grid (Sum.inr (scaledInterior α grid t))) x := by
      rw [supportWall_eq_affine U (normal α grid) x, supportWall_eq_affine U (normal α grid) x]
      exact h.2
    exact h2
  · have hfalse := hselected.symm.trans h.1
    simp [scaledSource] at hfalse

theorem second_source_le_first (U : Set Plane) (α : TerminalAngle)
    (hαL : (α : ℝ) < Real.pi / 2) (grid : Finset QuarterAngle)
    (t : InteriorPoint grid) {x : ℝ}
    (hx : x ∈ innerSourceSet U α hαL grid (scaledSource α grid (Sum.inr t))) :
    supportWall U (companionNormal (scaleAngle α t.val)) x ≤
      supportWall U (unitNormal (scaleAngle α t.val)) x := by
  classical
  let v : Option (SourceIndex α grid) → ℝ := fun i => wallSlope (normal α grid) i * x +
    barrierIntercept (normal α grid) (fun j => support U (normal α grid j)) i
  have hsource := niche_source_of_ne_terminal α hαL grid
    (scaledSource_ne_terminal α hαL grid (Sum.inr t)) (show
      (barrierExpr (pairList α grid) (some (terminalIndex α hαL grid))).source v =
        some (scaledSource α grid (Sum.inr t)) from hx)
  obtain ⟨ij, hij, hselected⟩ := nicheExpr_source_some hsource
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hij
  rcases cornerExpr_source_cases
      (Sum.inl (scaledInterior α grid s), Sum.inr (scaledInterior α grid s)) v with h | h
  · have hfalse := hselected.symm.trans h.1
    simp [scaledSource] at hfalse
  · have heq : t = s := scaledInterior_injective α grid
      (Sum.inr.inj (Option.some.inj (hselected.symm.trans h.1)))
    subst s
    have h2 : supportWall U (normal α grid (Sum.inr (scaledInterior α grid t))) x ≤
        supportWall U (normal α grid (Sum.inl (scaledInterior α grid t))) x := by
      rw [supportWall_eq_affine U (normal α grid) x, supportWall_eq_affine U (normal α grid) x]
      exact h.2
    exact h2

theorem above_barrier_wall_alternative {U : Set Plane} (hU : IsDownwardCap U)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2) (grid : Finset QuarterAngle)
    {p : Plane} (hp0 : 0 ≤ p.2)
    (hpB : finiteBarrier U (normal α grid) (pairList α grid)
      (some (terminalIndex α hαL grid)) p.1 ≤ p.2)
    {s : QuarterAngle} (hs : s ∈ grid) :
    support U (unitNormal (scaleAngle α s)) - 1 ≤ coordDot p (unitNormal (scaleAngle α s)) ∨
      support U (companionNormal (scaleAngle α s)) - 1 ≤
        coordDot p (companionNormal (scaleAngle α s)) := by
  by_cases hs0 : (s : ℝ) = 0
  · right
    have hscale : (scaleAngle α s : ℝ) = 0 := by
      simp only [scaleAngle, unitParameter, hs0, zero_div, mul_zero]
    have htop := hU.support_upward_le_one
    simpa only [hscale, companionNormal, Real.sin_zero, Real.cos_zero, neg_zero,
      coordDot, mul_zero, zero_add, mul_one] using
      (by linarith only [hp0, htop] : support U (0, 1) - 1 ≤ p.2)
  · have hspos : 0 < (scaleAngle α s : ℝ) := by
      exact mul_pos (TerminalAngle.pos α) (div_pos
        (lt_of_le_of_ne s.property.1 (Ne.symm hs0)) (by linarith [Real.pi_pos]))
    have hsL : (scaleAngle α s : ℝ) < Real.pi / 2 :=
      (scaleAngle_le_terminal α s).trans_lt hαL
    rw [finiteBarrier_eq_barrier] at hpB
    have hmin : cornerWall U (scaleAngle α s) p.1 ≤ p.2 :=
      (le_max_left _ _).trans ((clip_le_niche U α grid p.1 hs).trans
        ((le_max_left _ _).trans hpB))
    rcases min_le_iff.mp hmin with h | h
    · left
      rw [← supportWall_unitNormal] at h
      exact (supportWall_le_iff
        (Real.sin_pos_of_pos_of_lt_pi hspos (by linarith [Real.pi_pos])) p.1 p.2).mp h
    · right
      rw [← supportWall_companionNormal] at h
      exact (supportWall_le_iff
        (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hsL⟩) p.1 p.2).mp h

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
  let p : Plane := (x, y)
  let v := coordDot p (companionNormal (scaleAngle α t.val))
  have hy : finiteBarrier U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)) x = y :=
    innerSource_height U α hαL grid (scaledSource α grid (Sum.inl t)) hx
  have hy0 : 0 ≤ p.2 := by
    change 0 ≤ y
    rw [← hy]
    exact finiteBarrier_nonneg _ _ _ _ _
  have hline : coordDot p (unitNormal (scaleAngle α t.val)) = support U (unitNormal (scaleAngle α t.val)) - 1 := by
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
  refine ⟨v, ?_, mem_neighborParameters hc hs hv ?_ ?_⟩
  · have h := congrArg Prod.fst hp
    simpa only [p, wallPoint_fst] using h
  · rcases hm with h | h
    · left
      nlinarith
    · exact Or.inr h
  · rcases hp' with h | h
    · exact Or.inl h
    · right
      nlinarith

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
  let p : Plane := (x, y)
  let v := coordDot p (unitNormal (scaleAngle α t.val))
  have hy : finiteBarrier U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)) x = y :=
    innerSource_height U α hαL grid (scaledSource α grid (Sum.inr t)) hx
  have hy0 : 0 ≤ p.2 := by
    change 0 ≤ y
    rw [← hy]
    exact finiteBarrier_nonneg _ _ _ _ _
  have hline : coordDot p (companionNormal (scaleAngle α t.val)) = support U (companionNormal (scaleAngle α t.val)) - 1 := by
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
  refine ⟨v, ?_, mem_neighborParameters hc hs hv ?_ ?_⟩
  · have h := congrArg Prod.fst hp
    simpa only [p, companionPoint_fst] using h
  · rcases hp' with h | h
    · right
      nlinarith
    · left
      nlinarith
  · rcases hm with h | h
    · right
      nlinarith
    · left
      nlinarith

end PartialGrid

end AmbidextrousSofa
