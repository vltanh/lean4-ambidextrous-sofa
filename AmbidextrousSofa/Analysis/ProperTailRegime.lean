module

public import AmbidextrousSofa.Analysis.NegativeCompletion

@[expose] public section

/-!
# The local proper-tail regime

The terminal comparison needs only the two geometric conclusions left
after same-cap negative completion: a negative middle normal remains
unvisited, and the right middle height exceeds the terminal sine. They
hold as soon as the full-angle joint maximum produced by completion is
excluded. A largest-angle selection excludes it for the value reduction.
Full-cap affine rigidity excludes it for an individual equality cap,
without an extremal-angle selection.
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
  rcases lt_or_ge m 0 with hm | hm
  · exact (h.negative hm).1
  · unfold affineNormalAngle; linarith [Real.arctan_nonneg.mpr hm]

/-- Same-cap completion of a negative middle produces a joint maximum at the full angle, so the
tail regime holds whenever that maximum is excluded. -/
theorem IsJointCapMaximizer.properTailRegime_of_not_full
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hfull : m < 0 → ¬ IsJointCapMaximizer U (Real.pi / 2)) : ProperTailRegime U α m :=
  ⟨fun hm => (not_or.mp fun hcomplete => hfull hm (hU.full_jointMaximizer_of_negative_completion
    hproper hheight hm haffine hcomplete)).imp not_le.mp not_le.mp⟩

theorem IsJointCapMaximizer.properTailRegime_of_largest
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : ProperTailRegime U α m :=
  hU.properTailRegime_of_not_full hproper hheight haffine fun _ hfull =>
    hproper.not_ge (hLargest U _ hfull)

/-- The explicit rigidity input concerns this same cap at the completed
full angle. The completion inequality and the joint maximum construct
the required full maximum internally. -/
theorem IsJointCapMaximizer.properTailRegime_of_full_affine_rigidity
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hrigid : IsFullCapMaximizer U → m = 0) : ProperTailRegime U α m :=
  hU.properTailRegime_of_not_full hproper hheight haffine fun hm hfull => hm.ne
    (hrigid ⟨hfull.isCap, fun V hV => hfull.score_le hV ⟨by linarith [Real.pi_pos], le_rfl⟩⟩)

end AmbidextrousSofa
