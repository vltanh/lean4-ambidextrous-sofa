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
and is the intended cap. No approximation, selection, or limit property is
assumed as a certificate.
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
  classical
  obtain ⟨U, hU, hUB, hpoly, hmax⟩ := exists_boxed_selected_polygon
    (normal (dyadic level)) (fun i => (normal_snd_pos (dyadic level) i).le)
    (fun i => coefficient * stageWeight level i)
    (fun i => support target (normal (dyadic level) i)) (pairList (dyadic level)) none
    hTarget hTargetBox
  refine ⟨U, hU, hUB, hpoly, ?_⟩
  intro V hV hVB
  have h := hmax V hV hVB
  simpa only [sampledPenalty_mul, score, stagePenalty] using h

/-- The selected maximum's actual penalty is at most the selection
coefficient when the finite spatial error is at most its square. -/
theorem IsSelectedPolygon.penalty_le {target U : Set Plane} {a b coefficient : ℝ}
    {level : ℕ} (hU : IsSelectedPolygon target a b level coefficient U)
    (hTarget : IsFullCapMaximizer target)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hcoefficient : 0 < coefficient)
    (herror : score U (dyadic level) - capScore U (Real.pi / 2) ≤ coefficient ^ 2) :
    stagePenalty level target U ≤ coefficient := by
  have hselected := hU.maximizes target hTarget.isCap hTargetBox
  rw [stagePenalty_self, mul_zero, sub_zero] at hselected
  have hfinite := capScore_le_score hTarget.isCap (dyadic level)
  have hmax := hTarget.2 U hU.isCap
  apply (mul_le_mul_iff_right₀ hcoefficient).mp
  nlinarith

theorem exists_selected_approximations {target : Set Plane}
    (hTarget : IsFullCapMaximizer target) {a b : ℝ} (hab : a ≤ b)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1) :
    ∃ level : ℕ → ℕ, ∃ U : ℕ → Set Plane,
      (∀ n, n ≤ level n) ∧
      (∀ n, IsSelectedPolygon target a b (level n) (selectionRate n) (U n)) ∧
      ∀ n, stagePenalty (level n) target (U n) ≤ selectionRate n := by
  have hstage : ∀ n, ∃ level ≥ n, ∃ U : Set Plane,
      IsSelectedPolygon target a b level (selectionRate n) U ∧
        stagePenalty level target U ≤ selectionRate n := by
    intro n
    have hrate := selectionRate_pos n
    obtain ⟨level, hlevel, herror⟩ := exists_level_score_error_le hab (sq_pos_of_pos hrate) n
    obtain ⟨U, hU⟩ := exists_selected_polygon hTarget.isCap hTargetBox level (selectionRate n)
    exact ⟨level, hlevel, U, hU,
      hU.penalty_le hTarget hTargetBox hrate (herror U hU.isCap hU.inBox).2⟩
  choose level hlevel U hU hpenalty using hstage
  exact ⟨level, U, hlevel, hU, hpenalty⟩

/-- A vanishing persistent penalty identifies every actual Hausdorff
cluster point. The cap need not be smooth or have positive endpoint faces. -/
theorem eq_of_penalty_tendsto {target K : Set Plane} {U : ℕ → Set Plane}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target) (hK : IsDownwardCap K)
    (hU : ∀ n, IsDownwardCap (U n)) (hHausdorff : CapHausdorffTendsto U K)
    (hlevel : Tendsto level atTop atTop) (hcoefficient : Tendsto coefficient atTop (𝓝 0))
    (hpenalty : ∀ n, stagePenalty (level n) target (U n) ≤ coefficient n) : K = target := by
  apply eq_of_dyadic_support_eq hK hTarget
  intro m i
  let v : Plane := normal (dyadic m) i
  have hsupp := hHausdorff.support_tendsto (fun n => (hU n).isCompact)
    (fun n => (hU n).nonempty) hK.isCompact hK.nonempty v
  have hlim : Tendsto (fun n => levelWeight m * (support (U n) v - support target v) ^ 2)
      atTop (𝓝 (levelWeight m * (support K v - support target v) ^ 2)) :=
    ((hsupp.sub_const _).pow 2).const_mul _
  have hbound : ∀ᶠ n in atTop,
      levelWeight m * (support (U n) v - support target v) ^ 2 ≤ coefficient n := by
    filter_upwards [hlevel.eventually (eventually_ge_atTop m)] with n hn
    exact (persistent_sample_bound hn i target (U n)).trans (hpenalty n)
  have hle := le_of_tendsto_of_tendsto hlim hcoefficient hbound
  have hnonneg := mul_nonneg (levelWeight_pos m).le (sq_nonneg (support K v - support target v))
  have hzero : levelWeight m * (support K v - support target v) ^ 2 = 0 :=
    le_antisymm hle hnonneg
  have hsq : (support K v - support target v) ^ 2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (levelWeight_pos m).ne'
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)

/-- Every prescribed global spatial cap maximum is the Hausdorff limit
of actual selected dyadic polygon maxima in any containing fixed box.
The grid depth tends to infinity and the actual support-penalty coefficient
tends to zero. All endpoint degeneracies remain in this sequence. -/
theorem exists_selected_sequence {target : Set Plane}
    (hTarget : IsFullCapMaximizer target) {a b : ℝ} (hab : a ≤ b)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1) :
    ∃ level : ℕ → ℕ, ∃ coefficient : ℕ → ℝ, ∃ U : ℕ → Set Plane,
      (∀ n, n ≤ level n) ∧ (∀ n, 0 < coefficient n) ∧
      Tendsto coefficient atTop (𝓝 0) ∧
      (∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n)) ∧
      (∀ n, stagePenalty (level n) target (U n) ≤ coefficient n) ∧
      CapHausdorffTendsto U target := by
  obtain ⟨level, U, hlevel, hU, hpenalty⟩ :=
    exists_selected_approximations hTarget hab hTargetBox
  obtain ⟨K, hK, _, φ, hφ, hHausdorff⟩ := exists_cap_hausdorff_subsequence
    (fun n => (hU n).isCap) (isCompact_Icc.prod isCompact_Icc) (fun n => (hU n).inBox)
  have hlevelAtTop : Tendsto level atTop atTop := tendsto_atTop_mono hlevel tendsto_id
  have hKTarget : K = target := eq_of_penalty_tendsto hTarget.isCap hK
    (fun n => (hU (φ n)).isCap) hHausdorff (hlevelAtTop.comp hφ.tendsto_atTop)
    (selectionRate_tendsto.comp hφ.tendsto_atTop) (fun n => hpenalty (φ n))
  refine ⟨level ∘ φ, selectionRate ∘ φ, U ∘ φ, ?_,
    fun n => selectionRate_pos (φ n), selectionRate_tendsto.comp hφ.tendsto_atTop,
    fun n => hU (φ n), fun n => hpenalty (φ n), ?_⟩
  · intro n
    exact (hφ.le_apply).trans (hlevel (φ n))
  · simpa only [hKTarget] using hHausdorff

end AngularGrid

end AmbidextrousSofa
