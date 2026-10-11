module

public import AmbidextrousSofa.Analysis.PersistentPenalty
public import AmbidextrousSofa.Analysis.GridSeparation
public import AmbidextrousSofa.Analysis.GlobalCapMaximum

@[expose] public section

/-!
# Actual selected polygon sequences for a prescribed spatial maximum

At each stage compact maximization and exact-support circumscription give
an actual polygon. Its objective is the finite physical spatial score
minus a small persistent support penalty. Choosing the angular error below
the square of the penalty coefficient makes the unscaled penalty vanish.
Every Hausdorff cluster point then has all the prescribed sampled supports
and is the intended cap; this subsequence argument is shared with proper
angles. No approximation, selection, or limit property is assumed as a
certificate.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AmbidextrousSofa

namespace AngularGrid

open FinitePolygon

def IsSelectedPolygon (target : Set Plane) (a b : ℝ) (level : ℕ)
    (coefficient : ℝ) (U : Set Plane) : Prop :=
  IsDownwardCap U ∧ U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 ∧
    U = circumscription U (normal (dyadic level)) ∧
    ∀ V : Set Plane, IsDownwardCap V → V ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 →
      score V (dyadic level) - coefficient * stagePenalty level target V ≤
        score U (dyadic level) - coefficient * stagePenalty level target U

theorem IsSelectedPolygon.isCap {target U : Set Plane} {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) : IsDownwardCap U := hU.1

theorem IsSelectedPolygon.inBox {target U : Set Plane} {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) :
    U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 := hU.2.1

theorem IsSelectedPolygon.polygon_eq {target U : Set Plane} {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) :
    U = circumscription U (normal (dyadic level)) := hU.2.2.1

theorem IsSelectedPolygon.maximizes {target U : Set Plane} {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U)
    (V : Set Plane) (hV : IsDownwardCap V) (hVB : V ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1) :
    score V (dyadic level) - coefficient * stagePenalty level target V ≤
      score U (dyadic level) - coefficient * stagePenalty level target U := hU.2.2.2 V hV hVB

theorem exists_selected_polygon {target : Set Plane} (hTarget : IsDownwardCap target)
    {a b : ℝ} (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (level : ℕ) (coefficient : ℝ) :
    ∃ U : Set Plane, IsSelectedPolygon target a b level coefficient U := by
  simpa only [IsSelectedPolygon, sampledPenalty_mul, score, stagePenalty] using
    exists_boxed_selected_polygon (normal (dyadic level))
      (fun i => (normal_snd_pos (dyadic level) i).le) (fun i => coefficient * stageWeight level i)
      (fun i => support target (normal (dyadic level) i)) (pairList (dyadic level)) none
      hTarget hTargetBox

/-- A vanishing persistent penalty identifies every actual Hausdorff
cluster point. The cap need not be smooth or have positive endpoint faces. -/
theorem eq_of_penalty_tendsto {target K : Set Plane} {U : ℕ → Set Plane}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target) (hK : IsDownwardCap K)
    (hU : ∀ n, IsDownwardCap (U n)) (hHausdorff : CapHausdorffTendsto U K)
    (hlevel : Tendsto level atTop atTop) (hcoefficient : Tendsto coefficient atTop (𝓝 0))
    (hpenalty : ∀ n, stagePenalty (level n) target (U n) ≤ coefficient n) : K = target := by
  refine eq_of_dyadic_support_eq hK hTarget fun m i => ?_
  have hle := le_of_tendsto_of_tendsto
    ((((hHausdorff.support_tendsto (fun n => (hU n).isCompact) (fun n => (hU n).nonempty)
      hK.isCompact hK.nonempty _).sub_const _).pow 2).const_mul (levelWeight m)) hcoefficient
    (by filter_upwards [hlevel.eventually (eventually_ge_atTop m)] with n hn
        exact (persistent_sample_bound hn i target (U n)).trans (hpenalty n))
  have hsq : (support K (normal (dyadic m) i) - support target (normal (dyadic m) i)) ^ 2 ≤ 0 := by
    nlinarith [levelWeight_pos m]
  nlinarith

/-- Boxed caps with a property `P` at arbitrarily deep levels and selection rates, whose
penalties are at most those rates, have a subsequence converging to the target. -/
theorem exists_selected_sequence_of {target : Set Plane} (hTarget : IsDownwardCap target)
    {a b : ℝ} {P : ℕ → ℝ → Set Plane → Prop}
    (hP : ∀ n, ∃ level ≥ n, ∃ U, P level (selectionRate n) U ∧ IsDownwardCap U ∧
      U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 ∧ stagePenalty level target U ≤ selectionRate n) :
    ∃ level : ℕ → ℕ, ∃ coefficient : ℕ → ℝ, ∃ U : ℕ → Set Plane,
      (∀ n, n ≤ level n) ∧ (∀ n, 0 < coefficient n) ∧
      Tendsto coefficient atTop (𝓝 0) ∧ (∀ n, P (level n) (coefficient n) (U n)) ∧
      (∀ n, stagePenalty (level n) target (U n) ≤ coefficient n) ∧
      CapHausdorffTendsto U target := by
  choose level hlevel U hU hcap hbox hpenalty using hP
  obtain ⟨K, hK, -, φ, hφ, hHausdorff⟩ :=
    exists_cap_hausdorff_subsequence hcap (isCompact_Icc.prod isCompact_Icc) hbox
  obtain rfl : K = target := eq_of_penalty_tendsto hTarget hK (fun n => hcap (φ n)) hHausdorff
    ((tendsto_atTop_mono hlevel tendsto_id).comp hφ.tendsto_atTop)
    (selectionRate_tendsto.comp hφ.tendsto_atTop) fun n => hpenalty (φ n)
  exact ⟨level ∘ φ, selectionRate ∘ φ, U ∘ φ, fun n => hφ.le_apply.trans (hlevel (φ n)),
    fun n => selectionRate_pos (φ n), selectionRate_tendsto.comp hφ.tendsto_atTop,
    fun n => hU (φ n), fun n => hpenalty (φ n), hHausdorff⟩

/-- Every prescribed global spatial cap maximum is the Hausdorff limit
of actual selected dyadic polygon maxima in any containing fixed box.
The grid depth tends to infinity and the actual support-penalty coefficient
tends to zero. All endpoint degeneracies remain in this sequence. Choosing
the angular error below the square of the selection rate makes the
penalty at most that rate. -/
theorem exists_selected_sequence {target : Set Plane}
    (hTarget : IsFullCapMaximizer target) {a b : ℝ} (hab : a ≤ b)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1) :
    ∃ level : ℕ → ℕ, ∃ coefficient : ℕ → ℝ, ∃ U : ℕ → Set Plane,
      (∀ n, n ≤ level n) ∧ (∀ n, 0 < coefficient n) ∧
      Tendsto coefficient atTop (𝓝 0) ∧
      (∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n)) ∧
      (∀ n, stagePenalty (level n) target (U n) ≤ coefficient n) ∧
      CapHausdorffTendsto U target := by
  refine exists_selected_sequence_of (a := a) (b := b) hTarget.isCap fun n => ?_
  obtain ⟨level, hlevel, herror⟩ :=
    exists_level_score_error_le hab (sq_pos_of_pos (selectionRate_pos n)) n
  obtain ⟨U, hU⟩ := exists_selected_polygon hTarget.isCap hTargetBox level (selectionRate n)
  have hselected := hU.maximizes target hTarget.isCap hTargetBox
  rw [stagePenalty_self, mul_zero, sub_zero] at hselected
  exact ⟨level, hlevel, U, hU, hU.isCap, hU.inBox, by
    nlinarith [(herror target hTarget.isCap hTargetBox).1, hTarget.2 U hU.isCap,
      (herror U hU.isCap hU.inBox).2, selectionRate_pos n]⟩

end AngularGrid

/-- A cap lies in the box with unit slack around its horizontal projection. -/
theorem IsDownwardCap.subset_slack_box {U : Set Plane} (hU : IsDownwardCap U) :
    U ⊆ Icc (horizontalLeft U - 1) (horizontalRight U + 1) ×ˢ Icc (0 : ℝ) 1 := fun p hp => by
  have hx : p.1 ∈ Icc (horizontalLeft U) (horizontalRight U) :=
    hU.horizontalProjection_eq_Icc ▸ ⟨p, hp, rfl⟩
  exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, hU.inStrip hp⟩

/-- A full maximizer is the Hausdorff limit of selected dyadic polygons in its box with unit
slack, with levels tending to infinity and coefficients tending to zero. -/
theorem IsFullCapMaximizer.exists_selected_polygons {U : Set Plane}
    (hU : IsFullCapMaximizer U) :
    ∃ level : ℕ → ℕ, ∃ coefficient : ℕ → ℝ, ∃ V : ℕ → Set Plane,
      Tendsto level atTop atTop ∧ (∀ n, 0 ≤ coefficient n) ∧ Tendsto coefficient atTop (𝓝 0) ∧
      (∀ n, AngularGrid.IsSelectedPolygon U (horizontalLeft U - 1) (horizontalRight U + 1)
        (level n) (coefficient n) (V n)) ∧ CapHausdorffTendsto V U := by
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, -, hH⟩ :=
    AngularGrid.exists_selected_sequence hU (by linarith) hU.isCap.subset_slack_box
  exact ⟨level, coefficient, V, tendsto_atTop_mono hlevel tendsto_id, fun n => (hc n).le, hrate,
    hV, hH⟩

end AmbidextrousSofa
