module

public import AmbidextrousSofa.Analysis.NegativeCompletion

@[expose] public section

/-!
# The local proper-tail regime

The terminal comparison needs only the two geometric conclusions left
after same-cap negative completion: a negative middle normal remains
unvisited, and the right middle height exceeds the terminal sine. A
largest-angle selection supplies these conclusions for the value
reduction. Full-cap affine rigidity supplies the same conclusions for
an individual equality cap, without an extremal-angle selection.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

structure ProperTailRegime (U : Set Plane) (α m : ℝ) : Prop where
  negative : m < 0 → α < affineNormalAngle m ∧
    Real.sin α < capRoof U (horizontalRight U - capWidth U / 4)

theorem ProperTailRegime.terminal_lt_affineNormal
    {U : Set Plane} {α m : ℝ} (h : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2) : α < affineNormalAngle m := by
  by_cases hm : m < 0
  · exact (h.negative hm).1
  · have hm0 := Real.arctan_nonneg.mpr (le_of_not_gt hm)
    unfold affineNormalAngle
    linarith only [hm0, hproper]

theorem IsJointCapMaximizer.properTailRegime_of_largest
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : ProperTailRegime U α m :=
  ⟨fun hm => hU.negative_remaining_tail_geometry hLargest hproper hheight hm haffine⟩

theorem IsJointCapMaximizer.negative_remaining_tail_geometry_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1) (hm : m < 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    α < affineNormalAngle m ∧
      Real.sin α < capRoof U (horizontalRight U - capWidth U / 4) := hregime.negative hm

/-- The explicit rigidity input concerns this same cap at the completed
full angle. The completion inequality and the joint maximum construct
the required full maximum internally. -/
theorem IsJointCapMaximizer.properTailRegime_of_full_affine_rigidity
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hrigid : IsFullCapMaximizer U → m = 0) : ProperTailRegime U α m := by
  refine ⟨?_⟩
  intro hm
  have hnot : ¬(affineNormalAngle m ≤ α ∨
      capRoof U (horizontalRight U - capWidth U / 4) ≤ Real.sin α) := by
    intro hcomplete
    have hfull := hU.full_jointMaximizer_of_negative_completion
      hproper hheight hm haffine hcomplete
    have hfullCap : IsFullCapMaximizer U := ⟨hfull.isCap, fun V hV =>
      hfull.score_le hV ⟨by linarith only [Real.pi_pos], le_rfl⟩⟩
    exact hm.ne (hrigid hfullCap)
  exact ⟨lt_of_not_ge (fun h => hnot (Or.inl h)),
    lt_of_not_ge (fun h => hnot (Or.inr h))⟩

end AmbidextrousSofa
