import AmbidextrousSofa.Analysis.DyadicNeighbors

/-!
# Strict neighboring-wall shadowing for actual finite sources

The two neighboring corridor alternatives are retained together, before
the earlier two-interval overestimate. Strict separation can remove an
entire source or force it into its own wall interval. In the latter case
the actual curvature atom shortens that interval; the selected exposure
inequality then gives the half-mesh bound with its original errors.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

namespace AngularGrid

open FinitePolygon

def neighborFeasible (f g fm fp gm gp δ : ℝ) : Set ℝ :=
  {v | v ≤ g - 1 ∧
    (fm - 1 ≤ (f - 1) * Real.cos δ - v * Real.sin δ ∨
      gm - 1 ≤ (f - 1) * Real.sin δ + v * Real.cos δ) ∧
    (fp - 1 ≤ (f - 1) * Real.cos δ + v * Real.sin δ ∨
      gp - 1 ≤ -(f - 1) * Real.sin δ + v * Real.cos δ)}

theorem neighborFeasible_eq_empty_of_forward_separation
    {f g fm fp gm gp δ : ℝ} (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ)
    (hfirst : g - 1 < firstLo f fp δ)
    (hcompanion : g - 1 < companionPlus f gp δ) :
    neighborFeasible f g fm fp gm gp δ = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro v hv
  rcases hv.2.2 with h | h
  · have hlow : firstLo f fp δ ≤ v := by
      change (fp - 1 - (f - 1) * Real.cos δ) / Real.sin δ ≤ v
      rw [div_le_iff₀ hs]
      linarith
    exact not_lt_of_ge (hlow.trans hv.1) hfirst
  · have hlow : companionPlus f gp δ ≤ v := by
      change (gp - 1 + (f - 1) * Real.sin δ) / Real.cos δ ≤ v
      rw [div_le_iff₀ hc]
      linarith
    exact not_lt_of_ge (hlow.trans hv.1) hcompanion

theorem neighborFeasible_subset_self_interval
    {f g fm fp gm gp δ : ℝ} (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ)
    (hminus : g - 1 < companionMinus f gm δ)
    (hplus : firstHi f fm δ < companionPlus f gp δ) :
    neighborFeasible f g fm fp gm gp δ ⊆ Icc (firstLo f fp δ) (firstHi f fm δ) := by
  intro v hv
  have hm : ¬ gm - 1 ≤ (f - 1) * Real.sin δ + v * Real.cos δ := by
    intro h
    have hlow : companionMinus f gm δ ≤ v := by
      change (gm - 1 - (f - 1) * Real.sin δ) / Real.cos δ ≤ v
      rw [div_le_iff₀ hc]
      linarith
    exact not_lt_of_ge (hlow.trans hv.1) hminus
  have hupper : v ≤ firstHi f fm δ := by
    have h := hv.2.1.resolve_right hm
    change v ≤ ((f - 1) * Real.cos δ - fm + 1) / Real.sin δ
    rw [le_div_iff₀ hs]
    linarith
  have hp : ¬ gp - 1 ≤ -(f - 1) * Real.sin δ + v * Real.cos δ := by
    intro h
    have hlow : companionPlus f gp δ ≤ v := by
      change (gp - 1 + (f - 1) * Real.sin δ) / Real.cos δ ≤ v
      rw [div_le_iff₀ hc]
      linarith
    exact not_lt_of_ge (hlow.trans hupper) hplus
  refine ⟨?_, hupper⟩
  have h := hv.2.2.resolve_right hp
  change (fp - 1 - (f - 1) * Real.cos δ) / Real.sin δ ≤ v
  rw [div_le_iff₀ hs]
  linarith

theorem first_source_neighbor_feasible {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ : ℝ}
    (hminus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) + δ)
    {x : ℝ} (hx : x ∈ innerSourceSet U grid (Sum.inl t)) :
    ∃ v : ℝ, x = (support U (unitNormal t.val) - 1) * Real.cos t.val - v * Real.sin t.val ∧
      v ∈ neighborFeasible (support U (unitNormal t.val)) (support U (companionNormal t.val))
        (support U (unitNormal ((t.val : ℝ) - δ))) (support U (unitNormal ((t.val : ℝ) + δ)))
        (support U (companionNormal ((t.val : ℝ) - δ)))
        (support U (companionNormal ((t.val : ℝ) + δ))) δ := by
  let y := supportWall U (unitNormal t.val) x
  let p : Plane := (x, y)
  let v := coordDot p (companionNormal t.val)
  have hy : finiteBarrier U (normal grid) (pairList grid) none x = y :=
    innerSource_height U grid (Sum.inl t) hx
  have hy0 : 0 ≤ p.2 := by
    change 0 ≤ y
    rw [← hy]
    exact finiteBarrier_nonneg _ _ _ _ _
  have hline : coordDot p (unitNormal t.val) = support U (unitNormal t.val) - 1 := by
    apply le_antisymm
    · exact (le_supportWall_iff (normal_snd_pos grid (Sum.inl t)) x y).mp le_rfl
    · exact (supportWall_le_iff (normal_snd_pos grid (Sum.inl t)) x y).mp le_rfl
  have hp : p = wallPoint U t.val v := point_eq_wallPoint hline
  have hv : v ≤ support U (companionNormal t.val) - 1 :=
    (le_supportWall_iff (normal_snd_pos grid (Sum.inr t)) x y).mp
      (first_source_le_companion U grid t hx)
  obtain ⟨sm, hsm, hsmval⟩ := hminus
  obtain ⟨sp, hsp, hspval⟩ := hplus
  have hm := above_niche_wall_alternative hU grid hy0 hy.le hsm
  have hp' := above_niche_wall_alternative hU grid hy0 hy.le hsp
  rw [hsmval, hp, dot_wallPoint_first, dot_wallPoint_companion,
    show (t.val : ℝ) - δ - (t.val : ℝ) = -δ by ring,
    show (t.val : ℝ) - ((t.val : ℝ) - δ) = δ by ring,
    Real.cos_neg, Real.sin_neg] at hm
  rw [hspval, hp, dot_wallPoint_first, dot_wallPoint_companion,
    show (t.val : ℝ) + δ - (t.val : ℝ) = δ by ring,
    show (t.val : ℝ) - ((t.val : ℝ) + δ) = -δ by ring,
    Real.sin_neg, Real.cos_neg] at hp'
  refine ⟨v, ?_, hv, ?_, ?_⟩
  · have h := congrArg Prod.fst hp
    simpa only [p, wallPoint_fst] using h
  · rcases hm with h | h
    · exact Or.inl (by nlinarith)
    · exact Or.inr (by nlinarith)
  · rcases hp' with h | h
    · exact Or.inl (by nlinarith)
    · exact Or.inr (by nlinarith)

theorem second_source_neighbor_feasible {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ : ℝ}
    (hminus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) + δ)
    {x : ℝ} (hx : x ∈ innerSourceSet U grid (Sum.inr t)) :
    ∃ v : ℝ, x = -(support U (companionNormal t.val) - 1) * Real.sin t.val +
        v * Real.cos t.val ∧
      v ∈ neighborFeasible (support U (companionNormal t.val)) (support U (unitNormal t.val))
        (support U (companionNormal ((t.val : ℝ) + δ)))
        (support U (companionNormal ((t.val : ℝ) - δ)))
        (support U (unitNormal ((t.val : ℝ) + δ)))
        (support U (unitNormal ((t.val : ℝ) - δ))) δ := by
  let y := supportWall U (companionNormal t.val) x
  let p : Plane := (x, y)
  let v := coordDot p (unitNormal t.val)
  have hy : finiteBarrier U (normal grid) (pairList grid) none x = y :=
    innerSource_height U grid (Sum.inr t) hx
  have hy0 : 0 ≤ p.2 := by
    change 0 ≤ y
    rw [← hy]
    exact finiteBarrier_nonneg _ _ _ _ _
  have hline : coordDot p (companionNormal t.val) = support U (companionNormal t.val) - 1 := by
    apply le_antisymm
    · exact (le_supportWall_iff (normal_snd_pos grid (Sum.inr t)) x y).mp le_rfl
    · exact (supportWall_le_iff (normal_snd_pos grid (Sum.inr t)) x y).mp le_rfl
  have hp : p = companionPoint U t.val v := point_eq_companionPoint hline
  have hv : v ≤ support U (unitNormal t.val) - 1 :=
    (le_supportWall_iff (normal_snd_pos grid (Sum.inl t)) x y).mp
      (second_source_le_first U grid t hx)
  obtain ⟨sm, hsm, hsmval⟩ := hminus
  obtain ⟨sp, hsp, hspval⟩ := hplus
  have hm := above_niche_wall_alternative hU grid hy0 hy.le hsm
  have hp' := above_niche_wall_alternative hU grid hy0 hy.le hsp
  rw [hsmval, hp, dot_companionPoint_first, dot_companionPoint_companion,
    show (t.val : ℝ) - δ - (t.val : ℝ) = -δ by ring,
    show (t.val : ℝ) - ((t.val : ℝ) - δ) = δ by ring,
    Real.cos_neg, Real.sin_neg] at hm
  rw [hspval, hp, dot_companionPoint_first, dot_companionPoint_companion,
    show (t.val : ℝ) + δ - (t.val : ℝ) = δ by ring,
    show (t.val : ℝ) - ((t.val : ℝ) + δ) = -δ by ring,
    Real.sin_neg, Real.cos_neg] at hp'
  refine ⟨v, ?_, hv, ?_, ?_⟩
  · have h := congrArg Prod.fst hp
    simpa only [p, companionPoint_fst] using h
  · rcases hp' with h | h
    · exact Or.inr (by nlinarith)
    · exact Or.inl (by nlinarith)
  · rcases hm with h | h
    · exact Or.inr (by nlinarith)
    · exact Or.inl (by nlinarith)

theorem innerDensity_eq_zero_of_source_empty (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex grid) (hempty : innerSourceSet U grid j = ∅) :
    innerDensity U grid j = fun _ => 0 := by
  classical
  funext x
  have hnot : x ∉ innerSourceSet U grid j := by rw [hempty]; exact not_mem_empty x
  unfold innerDensity
  rw [outwardVelocity_eq_single, WallExpr.sourceDensity_single, indicator_of_notMem hnot]

theorem first_source_empty_of_forward_separation {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ)
    (hminus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) + δ)
    (hfirst : support U (companionNormal t.val) - 1 <
      firstLo (support U (unitNormal t.val)) (support U (unitNormal ((t.val : ℝ) + δ))) δ)
    (hcompanion : support U (companionNormal t.val) - 1 <
      companionPlus (support U (unitNormal t.val))
        (support U (companionNormal ((t.val : ℝ) + δ))) δ) :
    innerSourceSet U grid (Sum.inl t) = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro x hx
  obtain ⟨v, _, hv⟩ := first_source_neighbor_feasible hU grid t hminus hplus hx
  rw [neighborFeasible_eq_empty_of_forward_separation hc hs hfirst hcompanion] at hv
  exact not_mem_empty v hv

theorem second_source_empty_of_backward_separation {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ)
    (hminus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) + δ)
    (hfirst : support U (unitNormal t.val) - 1 <
      firstLo (support U (companionNormal t.val))
        (support U (companionNormal ((t.val : ℝ) - δ))) δ)
    (hcompanion : support U (unitNormal t.val) - 1 <
      companionPlus (support U (companionNormal t.val))
        (support U (unitNormal ((t.val : ℝ) - δ))) δ) :
    innerSourceSet U grid (Sum.inr t) = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro x hx
  obtain ⟨v, _, hv⟩ := second_source_neighbor_feasible hU grid t hminus hplus hx
  rw [neighborFeasible_eq_empty_of_forward_separation hc hs hfirst hcompanion] at hv
  exact not_mem_empty v hv

theorem integral_first_source_le_self_interval {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ a b : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ)
    (hh : Real.cos (δ / 2) ≠ 0) (hab : a ≤ b)
    (hminus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) + δ)
    (hsepMinus : support U (companionNormal t.val) - 1 <
      companionMinus (support U (unitNormal t.val))
        (support U (companionNormal ((t.val : ℝ) - δ))) δ)
    (hsepPlus : firstHi (support U (unitNormal t.val))
        (support U (unitNormal ((t.val : ℝ) - δ))) δ <
      companionPlus (support U (unitNormal t.val))
        (support U (companionNormal ((t.val : ℝ) + δ))) δ) :
    (∫ x in a..b, innerDensity U grid (Sum.inl t) x) ≤
      max (2 * Real.tan (δ / 2) - (upperCurvature U {t.val}).toReal) 0 := by
  classical
  have ht : 0 < Real.sin t.val := normal_snd_pos grid (Sum.inl t)
  have hint := integral_sourceDensity_outward (barrierExpr (pairList grid) none)
    (normal grid) (barrierIntercept (normal grid) (fun i => support U (normal grid i)))
    (Sum.inl t) hab
  change (∫ x in a..b, innerDensity U grid (Sum.inl t) x) =
    volume.real (Ioc a b ∩ innerSourceSet U grid (Sum.inl t)) / Real.sin t.val at hint
  rw [hint]
  have hbound := measure_parameterIntervals_le (S := Ioc a b ∩ innerSourceSet U grid (Sum.inl t))
    ht ((support U (unitNormal t.val) - 1) * Real.cos t.val)
    (firstLo (support U (unitNormal t.val)) (support U (unitNormal ((t.val : ℝ) + δ))) δ)
    (firstHi (support U (unitNormal t.val)) (support U (unitNormal ((t.val : ℝ) - δ))) δ)
    0 0 (by
      intro x hx
      obtain ⟨v, hvx, hv⟩ := first_source_neighbor_feasible hU grid t hminus hplus hx.2
      exact ⟨v, hvx, Or.inl (neighborFeasible_subset_self_interval hc hs hsepMinus hsepPlus hv)⟩)
  simp only [sub_self, max_self, add_zero] at hbound
  exact hbound.trans (max_le_max (first_interval_length_le_curvature hU t.val hs hh) le_rfl)

theorem integral_second_source_le_self_interval {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ a b : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ)
    (hh : Real.cos (δ / 2) ≠ 0) (hab : a ≤ b)
    (hminus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) + δ)
    (hsepPlus : support U (unitNormal t.val) - 1 <
      companionMinus (support U (companionNormal t.val))
        (support U (unitNormal ((t.val : ℝ) + δ))) δ)
    (hsepMinus : firstHi (support U (companionNormal t.val))
        (support U (companionNormal ((t.val : ℝ) + δ))) δ <
      companionPlus (support U (companionNormal t.val))
        (support U (unitNormal ((t.val : ℝ) - δ))) δ) :
    (∫ x in a..b, innerDensity U grid (Sum.inr t) x) ≤
      max (2 * Real.tan (δ / 2) - (upperCurvature U {t.val + Real.pi / 2}).toReal) 0 := by
  classical
  have ht : 0 < Real.cos t.val := normal_snd_pos grid (Sum.inr t)
  have hint := integral_sourceDensity_outward (barrierExpr (pairList grid) none)
    (normal grid) (barrierIntercept (normal grid) (fun i => support U (normal grid i)))
    (Sum.inr t) hab
  change (∫ x in a..b, innerDensity U grid (Sum.inr t) x) =
    volume.real (Ioc a b ∩ innerSourceSet U grid (Sum.inr t)) / Real.cos t.val at hint
  rw [hint]
  have hbound := measure_addParameterIntervals_le
    (S := Ioc a b ∩ innerSourceSet U grid (Sum.inr t)) ht
    (-(support U (companionNormal t.val) - 1) * Real.sin t.val)
    (firstLo (support U (companionNormal t.val))
      (support U (companionNormal ((t.val : ℝ) - δ))) δ)
    (firstHi (support U (companionNormal t.val))
      (support U (companionNormal ((t.val : ℝ) + δ))) δ) 0 0 (by
      intro x hx
      obtain ⟨v, hvx, hv⟩ := second_source_neighbor_feasible hU grid t hminus hplus hx.2
      exact ⟨v, hvx, Or.inl (neighborFeasible_subset_self_interval hc hs hsepPlus hsepMinus hv)⟩)
  simp only [sub_self, max_self, add_zero] at hbound
  exact hbound.trans (max_le_max (companion_interval_length_le_curvature hU t.val hs hh) le_rfl)

theorem IsSelectedPolygon.curvature_atom_le_error_of_source_empty {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hc : 0 ≤ coefficient)
    (j : SourceIndex (dyadic level)) (hempty : innerSourceSet U (dyadic level) j = ∅) :
    (upperCurvature U {fullAngle (dyadic level) j}).toReal ≤
      middleOuterMass U (dyadic level) j + selectionDefect target U level coefficient j := by
  have h := hU.curvature_atom_le hc j
  rw [innerDensity_eq_zero_of_source_empty U (dyadic level) j hempty,
    intervalIntegral.integral_zero, zero_add] at h
  exact h

theorem IsSelectedPolygon.curvature_atom_le_half_of_self_interval {target U : Set Plane}
    {a b coefficient d : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hc : 0 ≤ coefficient)
    (j : SourceIndex (dyadic level)) (hd : 0 ≤ d)
    (hsource : (∫ x in (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)..
        (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4),
          innerDensity U (dyadic level) j x) ≤
      max (2 * d - (upperCurvature U {fullAngle (dyadic level) j}).toReal) 0) :
    (upperCurvature U {fullAngle (dyadic level) j}).toReal ≤
      d + middleOuterMass U (dyadic level) j + selectionDefect target U level coefficient j := by
  have hatom := hU.curvature_atom_le hc j
  have herror := add_nonneg (middleOuterMass_nonneg hU.isCap (dyadic level) j)
    (selectionDefect_nonneg target U level hc j)
  have hbound : (upperCurvature U {fullAngle (dyadic level) j}).toReal ≤
      0 + max (2 * d - (upperCurvature U {fullAngle (dyadic level) j}).toReal) 0 +
        (middleOuterMass U (dyadic level) j + selectionDefect target U level coefficient j) := by
    change _ ≤ _ + middleOuterMass U (dyadic level) j +
      selectionDefect target U level coefficient j at hatom
    linarith
  have h := solve_curvature_self_bound herror hbound
  have heq : ((0 : ℝ) + 2 * d) / 2 = d := by ring
  simpa only [heq, max_eq_right hd, add_assoc] using h

end AngularGrid

end AmbidextrousSofa
