import AmbidextrousSofa.Analysis.InitialAngleBound
import AmbidextrousSofa.Analysis.TerminalScalar

/-!
# The actual preliminary width cut

The diagonal small-width estimate is independent of the cotangent and
inset. It therefore applies at every proper terminal angle once the two
actual endpoint alternatives have been obtained. Same-angle
canonicalization gives the width cut for an arbitrary proper-terminal
joint maximizer, without an initial-angle upper bound.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem IsDownwardCap.capScore_lt_forty_one_fiftieths_of_small_width_top_endpoint
    {U : Set Plane} (hU : IsDownwardCap U) {C α : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 49 / 100)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hα0 : Real.pi / 4 ≤ α) (hαL : α < Real.pi / 2)
    (htop : (-C, 1) ∈ U ∨ (C, 1) ∈ U) : capScore U α < (41 / 50 : ℝ) := by
  have hαpos : 0 < α := by linarith [Real.pi_pos]
  obtain ⟨_, _, hu1, hv1, _⟩ := hU.three_support_compatibility_centered hleft hright hα0 hαL
  have hhigh : C ≤ diagonalLeft U - 1 ∨ C ≤ diagonalRight U - 1 := by
    rcases htop with htop | htop
    · left
      simpa only [neg_neg] using (hU.three_support_lower_of_top hαpos hαL htop).1
    · exact Or.inr (hU.three_support_lower_of_top hαpos hαL htop).2.1
  have hsmall := initialAngleRelaxation_small_width hC0 hC1 hu1 hv1 hhigh
    (terminalSlope α) (terminalInset α) (terminalSupportPosition U α)
  exact (hU.capScore_le_initialAngleRelaxation hC0 hleft hright hα0 hαL).trans_lt hsmall

theorem IsJointCapMaximizer.centered_half_width_gt_forty_nine_hundredths
    {U : Set Plane} {C α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hαL : α < Real.pi / 2) (hC : 0 ≤ C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : (49 / 100 : ℝ) < C := by
  by_contra hbad
  have hw : capWidth U = 4 * C := by unfold capWidth; rw [hleft, hright]; ring
  have htop := hU.top_endpoint_of_affine hheight haffine
  rw [show horizontalLeft U + capWidth U / 4 = -C by rw [hleft, hw]; ring,
    show horizontalRight U - capWidth U / 4 = C by rw [hright, hw]; ring] at htop
  have hscore := hU.isCap.capScore_lt_forty_one_fiftieths_of_small_width_top_endpoint
    hC (le_of_not_gt hbad) hleft hright hU.angle_mem.1 hαL htop
  exact (not_lt_of_ge hU.reference_le) (hscore.trans forty_one_fiftieths_lt_half_M)

/-- The proper-terminal width cut applies to the original maximizer's
literal projection width; the canonical replacement preserves that width. -/
theorem IsJointCapMaximizer.width_gt_forty_nine_twenty_fifths
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α) (hαL : α < Real.pi / 2) :
    (49 / 25 : ℝ) < capWidth U := by
  have hcenter : IsJointCapMaximizer (centeredCap U) α :=
    hU.of_score_le hU.isCap.centeredCap hU.angle_mem
      (by simpa only [capScore_centeredCap hU.isCap] using le_refl (capScore U α))
  obtain ⟨V, hV, hproj, hheight, _, m, c, haffine⟩ := hcenter.exists_heightOne_affine_middle
  let C := capWidth U / 4
  have hC : 0 ≤ C := div_nonneg hU.isCap.capWidth_nonneg (by norm_num)
  have hleft : horizontalLeft V = -2 * C := by
    calc
      _ = horizontalLeft (centeredCap U) := by unfold horizontalLeft; rw [hproj]
      _ = _ := by rw [horizontalLeft_centeredCap hU.isCap]; dsimp [C]; ring
  have hright : horizontalRight V = 2 * C := by
    calc
      _ = horizontalRight (centeredCap U) := by unfold horizontalRight; rw [hproj]
      _ = _ := by rw [horizontalRight_centeredCap hU.isCap]; dsimp [C]; ring
  have hcut := hV.centered_half_width_gt_forty_nine_hundredths hαL hC hleft hright hheight haffine
  dsimp [C] at hcut
  linarith only [hcut]

end AmbidextrousSofa
