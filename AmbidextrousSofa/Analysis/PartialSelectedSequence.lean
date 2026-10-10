module

public import AmbidextrousSofa.Analysis.PartialGridScore
public import AmbidextrousSofa.Analysis.SelectedSequence
public import AmbidextrousSofa.Analysis.JointCapMaximum

@[expose] public section

/-!
# Actual selected proper-angle polygon sequences

Each selected polygon maximizes the finite physical score, with its whole
terminal wall, minus the persistent support penalty. The added rescaled
and terminal normals retain exactly the old support-separating penalty.
Uniform recovery of the proper-angle score and same-angle maximality force
that penalty to vanish. The selected sequence therefore converges to the
prescribed actual joint maximum.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AmbidextrousSofa

namespace PartialGrid

open FinitePolygon AngularGrid

def IsSelectedPolygon (target : Set Plane) (α : TerminalAngle)
    (hαL : (α : ℝ) < Real.pi / 2) (a b : ℝ) (level : ℕ)
    (coefficient : ℝ) (U : Set Plane) : Prop :=
  IsDownwardCap U ∧ U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 ∧
    U = circumscription U (normal α (dyadic level)) ∧
    ∀ V : Set Plane, IsDownwardCap V → V ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 →
      score V α hαL (dyadic level) - coefficient * AngularGrid.stagePenalty level target V ≤
        score U α hαL (dyadic level) - coefficient * AngularGrid.stagePenalty level target U

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

theorem IsSelectedPolygon.isCap {target U : Set Plane} {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U) : IsDownwardCap U := hU.1

theorem IsSelectedPolygon.inBox {target U : Set Plane} {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U) :
    U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 := hU.2.1

theorem IsSelectedPolygon.polygon_eq {target U : Set Plane} {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U) :
    U = circumscription U (normal α (dyadic level)) := hU.2.2.1

theorem IsSelectedPolygon.maximizes {target U : Set Plane} {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U)
    (V : Set Plane) (hV : IsDownwardCap V) (hVB : V ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1) :
    score V α hαL (dyadic level) - coefficient * AngularGrid.stagePenalty level target V ≤
      score U α hαL (dyadic level) - coefficient * AngularGrid.stagePenalty level target U :=
  hU.2.2.2 V hV hVB

theorem exists_selected_polygon {target : Set Plane} (hTarget : IsDownwardCap target)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    {a b : ℝ} (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (level : ℕ) (coefficient : ℝ) :
    ∃ U : Set Plane, IsSelectedPolygon target α hαL a b level coefficient U := by
  classical
  obtain ⟨U, hU, hUB, hpoly, hmax⟩ := exists_boxed_selected_polygon
    (normal α (dyadic level)) (fun i => (normal_snd_pos α (dyadic level) i).le)
    (fun i => coefficient * stageWeight α level i)
    (fun i => support target (normal α (dyadic level) i)) (pairList α (dyadic level))
    (some (terminalIndex α hαL (dyadic level))) hTarget hTargetBox
  refine ⟨U, hU, hUB, hpoly, ?_⟩
  intro V hV hVB
  have h := hmax V hV hVB
  simpa only [sampledPenalty_mul, sampledPenalty_eq_stagePenalty, score] using h

theorem IsSelectedPolygon.penalty_le {target U : Set Plane} {a b coefficient : ℝ}
    {level : ℕ} (hU : IsSelectedPolygon target α hαL a b level coefficient U)
    (hTarget : IsJointCapMaximizer target α)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hcoefficient : 0 < coefficient)
    (herror : score U α hαL (dyadic level) - capScore U α ≤ coefficient ^ 2) :
    AngularGrid.stagePenalty level target U ≤ coefficient := by
  have hselected := hU.maximizes target hTarget.isCap hTargetBox
  rw [AngularGrid.stagePenalty_self, mul_zero, sub_zero] at hselected
  have hfinite := capScore_le_score hTarget.isCap α hαL (dyadic level)
  have hmax := hTarget.score_le_same_angle hU.isCap
  apply (mul_le_mul_iff_right₀ hcoefficient).mp
  nlinarith

theorem exists_selected_approximations {target : Set Plane}
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    (hTarget : IsJointCapMaximizer target α) {a b : ℝ} (hab : a ≤ b)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1) :
    ∃ level : ℕ → ℕ, ∃ U : ℕ → Set Plane,
      (∀ n, n ≤ level n) ∧
      (∀ n, IsSelectedPolygon target α hαL a b (level n) (selectionRate n) (U n)) ∧
      ∀ n, AngularGrid.stagePenalty (level n) target (U n) ≤ selectionRate n := by
  have hstage : ∀ n, ∃ level ≥ n, ∃ U : Set Plane,
      IsSelectedPolygon target α hαL a b level (selectionRate n) U ∧
        AngularGrid.stagePenalty level target U ≤ selectionRate n := by
    intro n
    have hrate := selectionRate_pos n
    obtain ⟨level, hlevel, herror⟩ :=
      exists_level_score_error_le hab (sq_pos_of_pos hrate) α hαL n
    obtain ⟨U, hU⟩ := exists_selected_polygon hTarget.isCap α hαL hTargetBox level (selectionRate n)
    exact ⟨level, hlevel, U, hU,
      hU.penalty_le hTarget hTargetBox hrate (herror U hU.isCap hU.inBox).2⟩
  choose level hlevel U hU hpenalty using hstage
  exact ⟨level, U, hlevel, hU, hpenalty⟩

/-- The terminal angle is fixed and the target is the actual given
joint maximizer. Neither occupation nor a limiting score is a premise. -/
theorem exists_selected_sequence {target : Set Plane}
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    (hTarget : IsJointCapMaximizer target α) {a b : ℝ} (hab : a ≤ b)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1) :
    ∃ level : ℕ → ℕ, ∃ coefficient : ℕ → ℝ, ∃ U : ℕ → Set Plane,
      (∀ n, n ≤ level n) ∧ (∀ n, 0 < coefficient n) ∧
      Tendsto coefficient atTop (𝓝 0) ∧
      (∀ n, IsSelectedPolygon target α hαL a b (level n) (coefficient n) (U n)) ∧
      (∀ n, AngularGrid.stagePenalty (level n) target (U n) ≤ coefficient n) ∧
      CapHausdorffTendsto U target := by
  obtain ⟨level, U, hlevel, hU, hpenalty⟩ :=
    exists_selected_approximations α hαL hTarget hab hTargetBox
  obtain ⟨K, hK, _, φ, hφ, hHausdorff⟩ := exists_cap_hausdorff_subsequence
    (fun n => (hU n).isCap) (isCompact_Icc.prod isCompact_Icc) (fun n => (hU n).inBox)
  have hlevelAtTop : Tendsto level atTop atTop := tendsto_atTop_mono hlevel tendsto_id
  have hKTarget : K = target := AngularGrid.eq_of_penalty_tendsto hTarget.isCap hK
    (fun n => (hU (φ n)).isCap) hHausdorff (hlevelAtTop.comp hφ.tendsto_atTop)
    (selectionRate_tendsto.comp hφ.tendsto_atTop) (fun n => hpenalty (φ n))
  refine ⟨level ∘ φ, selectionRate ∘ φ, U ∘ φ, ?_,
    fun n => selectionRate_pos (φ n), selectionRate_tendsto.comp hφ.tendsto_atTop,
    fun n => hU (φ n), fun n => hpenalty (φ n), ?_⟩
  · intro n
    exact (hφ.le_apply).trans (hlevel (φ n))
  · simpa only [hKTarget] using hHausdorff

end PartialGrid

end AmbidextrousSofa
