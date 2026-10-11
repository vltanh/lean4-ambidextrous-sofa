module

public import AmbidextrousSofa.Analysis.InitialAngleBound
public import AmbidextrousSofa.Analysis.TerminalScalar

@[expose] public section

/-!
# The actual preliminary width cut

The diagonal small-width estimate is independent of the cotangent and
inset. It therefore applies at every proper terminal angle once the two
actual endpoint alternatives have been obtained. Same-angle
canonicalization gives the width cut for an arbitrary proper-terminal
joint maximizer, without an initial-angle upper bound: the maximizer is
recentered and replaced by its proved height-one affine-middle
representative, which has a top point above one of its middle endpoints.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

/-- A joint maximizer has a recentered height-one replacement at the same angle, with the same
width and a top point above one of its middle endpoints. -/
theorem IsJointCapMaximizer.exists_centered_top_endpoint {U : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) :
    ∃ V : Set Plane, IsJointCapMaximizer V α ∧
      horizontalLeft V = -2 * (capWidth U / 4) ∧ horizontalRight V = 2 * (capWidth U / 4) ∧
      ((-(capWidth U / 4), 1) ∈ V ∨ (capWidth U / 4, 1) ∈ V) := by
  obtain ⟨V, hV, hproj, hheight, -, m, c, haffine⟩ := (hU.of_score_le hU.isCap.centeredCap
    hU.angle_mem (capScore_centeredCap hU.isCap α).ge).exists_heightOne_affine_middle
  have hleft : horizontalLeft V = -2 * (capWidth U / 4) := (congrArg sInf hproj).trans
    (by rw [← horizontalLeft, horizontalLeft_centeredCap hU.isCap]; ring)
  have hright : horizontalRight V = 2 * (capWidth U / 4) := (congrArg sSup hproj).trans
    (by rw [← horizontalRight, horizontalRight_centeredCap hU.isCap]; ring)
  have htop := hV.top_endpoint_of_affine hheight haffine
  rw [capWidth, hleft, hright, show -2 * (capWidth U / 4) + (2 * (capWidth U / 4) -
    -2 * (capWidth U / 4)) / 4 = -(capWidth U / 4) by ring, show 2 * (capWidth U / 4) -
    (2 * (capWidth U / 4) - -2 * (capWidth U / 4)) / 4 = capWidth U / 4 by ring] at htop
  exact ⟨V, hV, hleft, hright, htop⟩

/-- A top point above a middle endpoint makes the left diagonal support or the terminal
support reach that endpoint. -/
theorem IsDownwardCap.three_support_high_of_top {U : Set Plane} (hU : IsDownwardCap U)
    {C α : ℝ} (hα0 : 0 < α) (hαL : α < Real.pi / 2) (htop : (-C, 1) ∈ U ∨ (C, 1) ∈ U) :
    C ≤ diagonalLeft U - 1 ∨ C ≤ terminalSupportPosition U α :=
  htop.imp (fun h => by simpa using (hU.three_support_lower_of_top hα0 hαL h).1)
    fun h => (hU.three_support_lower_of_top hα0 hαL h).2.2

theorem IsDownwardCap.capScore_lt_forty_one_fiftieths_of_small_width_top_endpoint
    {U : Set Plane} (hU : IsDownwardCap U) {C α : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 49 / 100)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hα0 : Real.pi / 4 ≤ α) (hαL : α < Real.pi / 2)
    (htop : (-C, 1) ∈ U ∨ (C, 1) ∈ U) : capScore U α < (41 / 50 : ℝ) := by
  obtain ⟨hbu, -, hu1, hv1, -⟩ := hU.three_support_compatibility_centered hleft hright hα0 hαL
  exact (hU.capScore_le_initialAngleRelaxation hC0 hleft hright hα0 hαL).trans_lt
    (initialAngleRelaxation_small_width hC0 hC1 hu1 hv1
      ((hU.three_support_high_of_top (by linarith [Real.pi_pos]) hαL htop).imp_right
        fun h => h.trans hbu) _ _ _)

/-- The proper-terminal width cut applies to the original maximizer's
literal projection width; the canonical replacement preserves that width. -/
theorem IsJointCapMaximizer.width_gt_forty_nine_twenty_fifths
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α) (hαL : α < Real.pi / 2) :
    (49 / 25 : ℝ) < capWidth U := by
  obtain ⟨V, hV, hleft, hright, htop⟩ := hU.exists_centered_top_endpoint
  by_contra! hbad
  linarith [hV.reference_le, forty_one_fiftieths_lt_half_M,
    hV.isCap.capScore_lt_forty_one_fiftieths_of_small_width_top_endpoint
      (div_nonneg hU.isCap.capWidth_nonneg (by norm_num)) (by linarith) hleft hright
      hV.angle_mem.1 hαL htop]

end AmbidextrousSofa
