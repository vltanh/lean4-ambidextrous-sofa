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
  obtain ⟨U, hU, hUB, hpoly, hmax⟩ := exists_boxed_selected_polygon
    (normal α (dyadic level)) (fun i => (normal_snd_pos α (dyadic level) i).le)
    (fun i => coefficient * stageWeight α level i)
    (fun i => support target (normal α (dyadic level) i)) (pairList α (dyadic level))
    (some (terminalIndex α hαL (dyadic level))) hTarget hTargetBox
  exact ⟨U, hU, hUB, hpoly, fun V hV hVB => by
    simpa only [sampledPenalty_mul, sampledPenalty_eq_stagePenalty, score] using hmax V hV hVB⟩

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
  refine exists_selected_sequence_of (a := a) (b := b) hTarget.isCap fun n => ?_
  obtain ⟨level, hlevel, herror⟩ :=
    exists_level_score_error_le hab (sq_pos_of_pos (selectionRate_pos n)) α hαL n
  obtain ⟨U, hU⟩ := exists_selected_polygon hTarget.isCap α hαL hTargetBox level (selectionRate n)
  have hselected := hU.maximizes target hTarget.isCap hTargetBox
  rw [AngularGrid.stagePenalty_self] at hselected
  exact ⟨level, hlevel, U, hU, hU.isCap, hU.inBox, by
    nlinarith [(herror target hTarget.isCap hTargetBox).1, hTarget.score_le_same_angle hU.isCap,
      (herror U hU.isCap hU.inBox).2, selectionRate_pos n]⟩

end PartialGrid

/-- A proper joint maximizer is the Hausdorff limit of selected polygons at its angle in its box
with unit slack, with levels tending to infinity and coefficients tending to zero. -/
theorem IsJointCapMaximizer.exists_selected_polygons {U : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) (hproper : α < Real.pi / 2) :
    ∃ level : ℕ → ℕ, ∃ coefficient : ℕ → ℝ, ∃ V : ℕ → Set Plane,
      Tendsto level atTop atTop ∧ (∀ n, 0 ≤ coefficient n) ∧ Tendsto coefficient atTop (𝓝 0) ∧
      (∀ n, PartialGrid.IsSelectedPolygon U ⟨α, hU.angle_mem⟩ hproper (horizontalLeft U - 1)
        (horizontalRight U + 1) (level n) (coefficient n) (V n)) ∧ CapHausdorffTendsto V U := by
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, -, hH⟩ :=
    PartialGrid.exists_selected_sequence ⟨α, hU.angle_mem⟩ hproper hU (by linarith)
      hU.isCap.subset_slack_box
  exact ⟨level, coefficient, V, tendsto_atTop_mono hlevel tendsto_id, fun n => (hc n).le, hrate,
    hV, hH⟩

end AmbidextrousSofa
