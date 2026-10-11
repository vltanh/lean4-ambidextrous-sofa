module

public import AmbidextrousSofa.Analysis.NeighborWalls

@[expose] public section

/-!
# Quantitative neighboring-wall source bounds

The literal finite niche source set is confined to two tangent intervals.
Their horizontal images give its actual Lebesgue measure. The second
interval is controlled by the actual Stieltjes curvature atom, using only
support inequalities at the two endpoints of the supporting face. This
does not require consecutive sampled walls to have nonzero facets.
-/

noncomputable section

open Set MeasureTheory MovingSofaOptimality

namespace AmbidextrousSofa

/-- The intervals may be empty or overlap. No disjointness assertion is
needed for this upper bound. -/
theorem measure_parameterIntervals_le {S : Set ℝ} {s : ℝ} (hs : 0 < s)
    (c a b d e : ℝ)
    (hS : ∀ x ∈ S, ∃ v : ℝ, x = c - v * s ∧ v ∈ Icc a b ∪ Icc d e) :
    volume.real S / s ≤ max (b - a) 0 + max (e - d) 0 := by
  have hsub : S ⊆ Icc (c - b * s) (c - a * s) ∪ Icc (c - e * s) (c - d * s) := by
    intro x hx
    obtain ⟨v, rfl, hv | hv⟩ := hS x hx
    · exact Or.inl ⟨by nlinarith [hv.2], by nlinarith [hv.1]⟩
    · exact Or.inr ⟨by nlinarith [hv.2], by nlinarith [hv.1]⟩
  rw [div_le_iff₀ hs]
  refine ((measureReal_mono hsub (measure_union_lt_top measure_Icc_lt_top
    measure_Icc_lt_top).ne).trans (measureReal_union_le _ _)).trans_eq ?_
  rw [Real.volume_real_Icc, Real.volume_real_Icc, add_mul, max_mul_of_nonneg _ _ hs.le,
    max_mul_of_nonneg _ _ hs.le, zero_mul]
  congr 2 <;> ring

/-- Every actual face atom is bounded by the support second difference.
The inequality is obtained at the two actual endpoints of that face. -/
theorem IsDownwardCap.curvature_atom_mul_sin_le {U : Set Plane}
    (hU : IsDownwardCap U) (t δ : ℝ) :
    (upperCurvature U {t}).toReal * Real.sin δ ≤
      support U (unitNormal (t - δ)) + support U (unitNormal (t + δ)) -
        2 * Real.cos δ * support U (unitNormal t) := by
  have hK := hU.imported_isConvexBody
  have hm := dot_le_supp hU.isCompact (vminus_mem_edge hK t).1 (t - δ)
  have hp := dot_le_supp hU.isCompact (vplus_mem_edge hK t).1 (t + δ)
  rw [dot_uvec_eq_cos_add_sin _ (t - δ) t, sub_sub_cancel_left, Real.cos_neg, Real.sin_neg,
    dot_vminus_uvec] at hm
  rw [dot_uvec_eq_cos_add_sin _ (t + δ) t, add_sub_cancel_left, dot_vplus_uvec] at hp
  change sigmaAt U t * Real.sin δ ≤ supp U (t - δ) + supp U (t + δ) - 2 * Real.cos δ * supp U t
  rw [sigmaAt_eq_dot_sub hK]
  linarith

theorem IsDownwardCap.support_secondDifference_nonneg {U : Set Plane}
    (hU : IsDownwardCap U) (t : ℝ) {δ : ℝ} (hs : 0 ≤ Real.sin δ) :
    0 ≤ support U (unitNormal (t - δ)) + support U (unitNormal (t + δ)) -
      2 * Real.cos δ * support U (unitNormal t) :=
  (mul_nonneg ENNReal.toReal_nonneg hs).trans (hU.curvature_atom_mul_sin_le t δ)

theorem IsDownwardCap.companion_secondDifference_nonneg {U : Set Plane}
    (hU : IsDownwardCap U) (t : ℝ) {δ : ℝ} (hs : 0 ≤ Real.sin δ) :
    0 ≤ support U (companionNormal (t - δ)) + support U (companionNormal (t + δ)) -
      2 * Real.cos δ * support U (companionNormal t) := by
  have h := hU.support_secondDifference_nonneg (t + Real.pi / 2) hs
  rw [add_sub_right_comm t, add_right_comm t] at h
  simpa only [← companionNormal_eq_unitNormal] using h

namespace AngularGrid

open FinitePolygon

def firstCornerSecant (U : Set Plane) (t δ : ℝ) : ℝ :=
  support U (unitNormal t) +
    (support U (companionNormal (t + δ)) -
      support U (companionNormal t) * Real.cos δ) / Real.sin δ - 1

theorem companion_interval_length_le {f g gm gp δ : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ)
    (hh : Real.cos (δ / 2) ≠ 0)
    (hconv : 0 ≤ gm + gp - 2 * Real.cos δ * g) :
    max (g - 1 - min (companionMinus f gm δ) (companionPlus f gp δ)) 0 ≤
      Real.tan δ * (|f + (gp - g * Real.cos δ) / Real.sin δ - 1| + Real.tan (δ / 2)) := by
  set q := f + (gp - g * Real.cos δ) / Real.sin δ - 1 with hq
  have hT : Real.tan (δ / 2) = (1 - Real.cos δ) / Real.sin δ := by
    rw [← tan_half_mul_sin hh]; field_simp
  have htan : 0 ≤ Real.tan δ := by rw [Real.tan_eq_sin_div_cos]; positivity
  have hqm : (g * Real.cos δ - gm) / Real.sin δ ≤ (gp - g * Real.cos δ) / Real.sin δ :=
    div_le_div_of_nonneg_right (by linarith) hs.le
  -- Both endpoints are `tan δ * (± secant + tan (δ / 2))`, the first with a smaller secant.
  have hm : g - 1 - companionMinus f gm δ =
      Real.tan δ * ((f + (g * Real.cos δ - gm) / Real.sin δ - 1) + Real.tan (δ / 2)) := by
    rw [companionMinus, Real.tan_eq_sin_div_cos, hT]
    field_simp
    ring
  have hp : g - 1 - companionPlus f gp δ = Real.tan δ * (-q + Real.tan (δ / 2)) := by
    rw [companionPlus, Real.tan_eq_sin_div_cos, hT, hq]
    field_simp
    ring
  rw [sub_inf, hm, hp]
  exact max_le (max_le (mul_le_mul_of_nonneg_left (by linarith [le_abs_self q]) htan)
    (mul_le_mul_of_nonneg_left (by linarith [neg_le_abs q]) htan))
    (mul_nonneg htan (add_nonneg (abs_nonneg q)
      (hT ▸ div_nonneg (by linarith [Real.cos_le_one δ]) hs.le)))

theorem first_interval_length_le_curvature {U : Set Plane} (hU : IsDownwardCap U)
    (t : ℝ) {δ : ℝ} (hs : 0 < Real.sin δ) (hh : Real.cos (δ / 2) ≠ 0) :
    firstHi (support U (unitNormal t)) (support U (unitNormal (t - δ))) δ -
      firstLo (support U (unitNormal t)) (support U (unitNormal (t + δ))) δ ≤
        2 * Real.tan (δ / 2) - (upperCurvature U {t}).toReal := by
  have heq :
      (firstHi (support U (unitNormal t)) (support U (unitNormal (t - δ))) δ -
        firstLo (support U (unitNormal t)) (support U (unitNormal (t + δ))) δ) * Real.sin δ =
      2 - 2 * Real.cos δ -
        (support U (unitNormal (t - δ)) + support U (unitNormal (t + δ)) -
          2 * Real.cos δ * support U (unitNormal t)) := by
    unfold firstHi firstLo
    field_simp
    ring
  exact (mul_le_mul_iff_left₀ hs).mp (by
    linarith [hU.curvature_atom_mul_sin_le t δ, tan_half_mul_sin hh])

theorem integral_first_source_le_parameters {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ a b : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ) (hab : a ≤ b)
    (hminus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) + δ) :
    (∫ x in a..b, innerDensity U grid (Sum.inl t) x) ≤
      max (support U (companionNormal t.val) - 1 -
        min (companionMinus (support U (unitNormal t.val))
          (support U (companionNormal ((t.val : ℝ) - δ))) δ)
          (companionPlus (support U (unitNormal t.val))
            (support U (companionNormal ((t.val : ℝ) + δ))) δ)) 0 +
      max (firstHi (support U (unitNormal t.val))
          (support U (unitNormal ((t.val : ℝ) - δ))) δ -
        firstLo (support U (unitNormal t.val))
          (support U (unitNormal ((t.val : ℝ) + δ))) δ) 0 := by
  classical
  exact (integral_sourceDensity_outward (barrierExpr (pairList grid) none) (normal grid)
    (barrierIntercept (normal grid) (fun i => support U (normal grid i))) (Sum.inl t) hab).trans_le
    (measure_parameterIntervals_le (normal_snd_pos grid (Sum.inl t))
      ((support U (unitNormal t.val) - 1) * Real.cos t.val) _ _ _ _
      fun x hx => first_source_neighbor_parameters hU grid t hc hs hminus hplus hx.2)

/-- The refined first-wall source estimate for the actual finite niche,
on any ordered spatial integration interval. -/
theorem integral_first_source_le {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (t : InteriorPoint grid) {δ a b : ℝ}
    (hc : 0 < Real.cos δ) (hs : 0 < Real.sin δ)
    (hh : Real.cos (δ / 2) ≠ 0) (hab : a ≤ b)
    (hminus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) - δ)
    (hplus : ∃ s ∈ grid, (s : ℝ) = (t.val : ℝ) + δ) :
    (∫ x in a..b, innerDensity U grid (Sum.inl t) x) ≤
      Real.tan δ * (|firstCornerSecant U t.val δ| + Real.tan (δ / 2)) +
        max (2 * Real.tan (δ / 2) - (upperCurvature U {(t.val : ℝ)}).toReal) 0 :=
  (integral_first_source_le_parameters hU grid t hc hs hab hminus hplus).trans
    (add_le_add (companion_interval_length_le hc hs hh
      (hU.companion_secondDifference_nonneg t.val hs.le))
      (max_le_max (first_interval_length_le_curvature hU t.val hs hh) le_rfl))

end AngularGrid

end AmbidextrousSofa
