module

public import AmbidextrousSofa.Analysis.InitialAngleBound
public import AmbidextrousSofa.Analysis.TerminalScalar

@[expose] public section

/-!
# The actual initial-angle exclusion for joint cap maximizers

The real terminal angle determines the cotangent range and inset relation
used by the all-width scalar estimate. Actual top endpoints determine its
support alternative. Consequently every centered cap with such a top
endpoint has the strict AT margin throughout the initial angle interval.

An arbitrary joint maximizer is recentered and then replaced by its
proved height-one affine-middle representative at the same angle. This
discharges every scalar hypothesis and excludes that interval for all
joint maximizers. No full-angle sharp value is assumed.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem terminalSlope_mem_initialAngle_interval {α : ℝ}
    (hα0 : Real.arctan (5 / 4) ≤ α) (hα1 : α ≤ Real.arctan (8 / 3)) :
    3 / 8 ≤ terminalSlope α ∧ terminalSlope α ≤ 4 / 5 := by
  have hαpos : 0 < α :=
    (Real.arctan_pos.mpr (by norm_num : (0 : ℝ) < 5 / 4)).trans_le hα0
  have hαL : α < Real.pi / 2 := hα1.trans_lt (Real.arctan_lt_pi_div_two (8 / 3))
  have hαmem : α ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], hαL⟩
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hαpos
    (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo hαmem
  have htan0 : 5 / 4 ≤ Real.tan α := by
    have h := Real.strictMonoOn_tan.monotoneOn (Real.arctan_mem_Ioo (5 / 4)) hαmem hα0
    simpa only [Real.tan_arctan] using h
  have htan1 : Real.tan α ≤ 8 / 3 := by
    have h := Real.strictMonoOn_tan.monotoneOn hαmem (Real.arctan_mem_Ioo (8 / 3)) hα1
    simpa only [Real.tan_arctan] using h
  rw [Real.tan_eq_sin_div_cos] at htan0 htan1
  have hsc0 := (le_div_iff₀ hc).1 htan0
  have hsc1 := (div_le_iff₀ hc).1 htan1
  unfold terminalSlope
  constructor
  · apply (le_div_iff₀ hs).2
    linarith only [hsc1]
  · apply (div_le_iff₀ hs).2
    linarith only [hsc0]

/-- The actual support geometry at either middle top endpoint discharges
the all-width scalar hypotheses. This is a bound on the literal cap score. -/
theorem IsDownwardCap.capScore_lt_initialAngle_rational_of_top_endpoint
    {U : Set Plane} (hU : IsDownwardCap U) {C α : ℝ} (hC : 0 ≤ C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hα0 : Real.pi / 4 ≤ α) (hα1 : α ≤ Real.arctan (8 / 3))
    (htop : (-C, 1) ∈ U ∨ (C, 1) ∈ U) :
    capScore U α < (5259 / 6400 : ℝ) := by
  have hαpos : 0 < α := by linarith [Real.pi_pos]
  have hαL : α < Real.pi / 2 := hα1.trans_lt (Real.arctan_lt_pi_div_two (8 / 3))
  by_cases hlow : α ≤ Real.arctan (5 / 4)
  · calc
      _ ≤ (1 + 1 / Real.sin α) ^ 2 / (8 * (Real.cos α / Real.sin α)) :=
        hU.capScore_le_terminal_bound hαpos hαL
      _ ≤ (33 + 5 * Real.sqrt 41) / 80 := terminal_bound_le_arctan_five_fourths hα0 hlow
      _ < (1301 / 1600 : ℝ) := terminal_exact_bound_lt_rational
      _ < (5259 / 6400 : ℝ) := by norm_num
  · have hk := terminalSlope_mem_initialAngle_interval (le_of_not_ge hlow) hα1
    obtain ⟨hbu, hcompat, hu1, hv1, hb1⟩ :=
      hU.three_support_compatibility_centered hleft hright hα0 hαL
    have hhigh : C ≤ diagonalLeft U - 1 ∨ C ≤ terminalSupportPosition U α := by
      rcases htop with htop | htop
      · left
        simpa only [neg_neg] using (hU.three_support_lower_of_top hαpos hαL htop).1
      · exact Or.inr (hU.three_support_lower_of_top hαpos hαL htop).2.2
    have hscalar := initialAngleRelaxation_all_width_lt (C := C)
      (k := terminalSlope α) (d := terminalInset α)
      (s := Real.sqrt (1 + terminalSlope α ^ 2))
      (u := diagonalRight U - 1) (v := diagonalLeft U - 1)
      (b := terminalSupportPosition U α) hC hk.1 hk.2
      (Real.sqrt_nonneg _) (Real.sq_sqrt (by positivity))
      (terminalSlope_mul_inset hαpos hαL) hbu hu1 hv1 hb1 hcompat hhigh
    exact (hU.capScore_le_initialAngleRelaxation hC hleft hright hα0 hαL).trans_lt hscalar

theorem IsJointCapMaximizer.terminal_angle_gt_arctan_eight_thirds_of_centered
    {U : Set Plane} {C α m c : ℝ} (hU : IsJointCapMaximizer U α) (hC : 0 ≤ C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : Real.arctan (8 / 3) < α := by
  by_contra hbad
  have hα1 : α ≤ Real.arctan (8 / 3) := le_of_not_gt hbad
  have hw : capWidth U = 4 * C := by unfold capWidth; rw [hleft, hright]; ring
  have htop := hU.top_endpoint_of_affine hheight haffine
  rw [show horizontalLeft U + capWidth U / 4 = -C by rw [hleft, hw]; ring,
    show horizontalRight U - capWidth U / 4 = C by rw [hright, hw]; ring] at htop
  have hscore := hU.isCap.capScore_lt_initialAngle_rational_of_top_endpoint
    hC hleft hright hU.angle_mem.1 hα1 htop
  exact (not_lt_of_ge hU.reference_le) (hscore.trans initialAngle_rational_lt_half_M)

/-- Every actual joint cap maximizer has terminal angle beyond AT's
initial interval. Recentring and canonicalization preserve its own angle
and maximizing score before the proved top-endpoint bound is applied. -/
theorem IsJointCapMaximizer.terminal_angle_gt_arctan_eight_thirds
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α) :
    Real.arctan (8 / 3) < α := by
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
  exact hV.terminal_angle_gt_arctan_eight_thirds_of_centered hC hleft hright hheight haffine

end AmbidextrousSofa
