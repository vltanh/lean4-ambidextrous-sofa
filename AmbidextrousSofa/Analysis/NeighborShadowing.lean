module

public import AmbidextrousSofa.Analysis.DyadicNeighbors

@[expose] public section

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

theorem neighborFeasible_eq_empty_of_forward_separation
    {f g fm fp gm gp δ : ℝ} (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ)
    (hfirst : g - 1 < firstLo f fp δ)
    (hcompanion : g - 1 < companionPlus f gp δ) :
    neighborFeasible f g fm fp gm gp δ = ∅ := by
  refine eq_empty_of_forall_notMem fun v ⟨hv, _, h⟩ => ?_
  rw [firstLo, lt_div_iff₀ hs] at hfirst
  rw [companionPlus, lt_div_iff₀ hc] at hcompanion
  rcases h with h | h
  · linarith [mul_le_mul_of_nonneg_right hv hs.le]
  · linarith [mul_le_mul_of_nonneg_right hv hc.le]

theorem neighborFeasible_le_firstHi_of_one_separation
    {f g fm fp gm gp δ v : ℝ} (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ)
    (hminus : g - 1 < companionMinus f gm δ)
    (hv : v ∈ neighborFeasible f g fm fp gm gp δ) :
    v ≤ firstHi f fm δ := by
  have hm : ¬ gm - 1 ≤ (f - 1) * Real.sin δ + v * Real.cos δ := fun h =>
    hminus.not_ge (((div_le_iff₀ hc).2 (by linarith)).trans hv.1)
  exact (le_div_iff₀ hs).2 (by linarith [hv.2.1.resolve_right hm])

theorem neighborFeasible_subset_self_interval
    {f g fm fp gm gp δ : ℝ} (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ)
    (hminus : g - 1 < companionMinus f gm δ)
    (hplus : firstHi f fm δ < companionPlus f gp δ) :
    neighborFeasible f g fm fp gm gp δ ⊆ Icc (firstLo f fp δ) (firstHi f fm δ) := fun v hv => by
  have hupper := neighborFeasible_le_firstHi_of_one_separation hc hs hminus hv
  rw [companionPlus, lt_div_iff₀ hc] at hplus
  refine ⟨?_, hupper⟩
  rw [firstLo, div_le_iff₀ hs]
  rcases hv.2.2 with h | h <;> linarith [mul_le_mul_of_nonneg_right hupper hc.le]

theorem innerDensity_eq_zero_of_source_empty (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex grid) (hempty : innerSourceSet U grid j = ∅) :
    innerDensity U grid j = fun _ => 0 := by
  funext x
  rw [innerDensity, outwardVelocity_eq_single, WallExpr.sourceDensity_single]
  exact indicator_of_notMem (hempty ▸ notMem_empty x : x ∉ innerSourceSet U grid j) _

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
    innerSourceSet U grid (Sum.inl t) = ∅ :=
  eq_empty_of_forall_notMem fun _ hx => by
    obtain ⟨v, _, hv⟩ := first_source_neighbor_feasible hU grid t hminus hplus hx
    exact (neighborFeasible_eq_empty_of_forward_separation hc hs hfirst hcompanion).subset hv

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
    innerSourceSet U grid (Sum.inr t) = ∅ :=
  eq_empty_of_forall_notMem fun _ hx => by
    obtain ⟨v, _, hv⟩ := second_source_neighbor_feasible hU grid t hminus hplus hx
    exact (neighborFeasible_eq_empty_of_forward_separation hc hs hfirst hcompanion).subset hv

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
      max (2 * Real.tan (δ / 2) - (upperCurvature U {(t.val : ℝ)}).toReal) 0 := by
  have h := measure_parameterIntervals_le (S := Ioc a b ∩ innerSourceSet U grid (Sum.inl t))
    (normal_snd_pos grid (Sum.inl t)) ((support U (unitNormal t.val) - 1) * Real.cos t.val)
    _ _ 0 0 fun x hx => (first_source_neighbor_feasible hU grid t hminus hplus hx.2).imp
      fun v hv => ⟨hv.1, .inl (neighborFeasible_subset_self_interval hc hs hsepMinus hsepPlus hv.2)⟩
  rw [sub_self, max_self, add_zero] at h
  exact (integral_sourceDensity_outward _ (normal grid) _ (Sum.inl t) hab).trans_le
    (h.trans (max_le_max (first_interval_length_le_curvature hU t.val hs hh) le_rfl))

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
  have h := measure_addParameterIntervals_le (S := Ioc a b ∩ innerSourceSet U grid (Sum.inr t))
    (normal_snd_pos grid (Sum.inr t)) (-(support U (companionNormal t.val) - 1) * Real.sin t.val)
    _ _ 0 0 fun x hx => (second_source_neighbor_feasible hU grid t hminus hplus hx.2).imp
      fun v hv => ⟨hv.1, .inl (neighborFeasible_subset_self_interval hc hs hsepPlus hsepMinus hv.2)⟩
  rw [sub_self, max_self, add_zero] at h
  exact (integral_sourceDensity_outward _ (normal grid) _ (Sum.inr t) hab).trans_le
    (h.trans (max_le_max (companion_interval_length_le_curvature hU t.val hs hh) le_rfl))

theorem IsSelectedPolygon.curvature_atom_le_error_of_source_empty {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hc : 0 ≤ coefficient)
    (j : SourceIndex (dyadic level)) (hempty : innerSourceSet U (dyadic level) j = ∅) :
    (upperCurvature U {fullAngle (dyadic level) j}).toReal ≤
      middleOuterMass U (dyadic level) j + selectionDefect target U level coefficient j := by
  have h := hU.curvature_atom_le hc j
  rwa [innerDensity_eq_zero_of_source_empty U _ j hempty, intervalIntegral.integral_zero,
    zero_add] at h

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
  have := hU.curvature_atom_le hc j
  have := middleOuterMass_nonneg hU.isCap (dyadic level) j
  have := selectionDefect_nonneg target U level hc j
  unfold middleOuterMass at *
  rcases max_cases (2 * d - (upperCurvature U {fullAngle (dyadic level) j}).toReal) 0 with h | h <;>
    linarith [h.1, h.2]

end AngularGrid

end AmbidextrousSofa
