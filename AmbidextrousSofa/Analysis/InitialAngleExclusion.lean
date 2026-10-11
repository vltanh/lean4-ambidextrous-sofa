module

public import AmbidextrousSofa.Analysis.InitialAngleBound
public import AmbidextrousSofa.Analysis.TerminalScalar

@[expose] public section

/-!
# The actual initial-angle exclusion for joint cap maximizers

The real terminal angle determines the cotangent range and inset relation
used by the all-width scalar estimate. Actual top endpoints determine its
support alternative. Consequently every centered cap with such a top
endpoint has a strict margin throughout the initial angle interval.

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
  have hα : 0 < α := (Real.arctan_pos.mpr (by norm_num)).trans_le hα0
  have hαL : α < Real.pi / 2 := hα1.trans_lt (Real.arctan_lt_pi_div_two _)
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαL⟩
  rw [← Real.arctan_tan (by linarith [Real.pi_pos]) hαL, Real.arctan_le_arctan_iff,
    Real.tan_eq_sin_div_cos] at hα0 hα1
  rw [le_div_iff₀ hc] at hα0
  rw [div_le_iff₀ hc] at hα1
  unfold terminalSlope
  constructor
  · rw [le_div_iff₀ hs]; linarith
  · rw [div_le_iff₀ hs]; linarith

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
  rcases le_or_gt α (Real.arctan (5 / 4)) with hlow | hlow
  · linarith [hU.capScore_le_terminal_bound hαpos hαL,
      terminal_bound_le_arctan_five_fourths hα0 hlow, terminal_exact_bound_lt_rational]
  have hk := terminalSlope_mem_initialAngle_interval hlow.le hα1
  obtain ⟨hbu, hcompat, hu1, hv1, hb1⟩ :=
    hU.three_support_compatibility_centered hleft hright hα0 hαL
  refine (hU.capScore_le_initialAngleRelaxation hC hleft hright hα0 hαL).trans_lt
    (initialAngleRelaxation_all_width_lt hC hk.1 hk.2 (Real.sqrt_nonneg _)
      (Real.sq_sqrt (by positivity)) (terminalSlope_mul_inset hαpos hαL) hbu hu1 hv1 hb1
      hcompat ?_)
  rcases htop with htop | htop
  · exact .inl (by simpa using (hU.three_support_lower_of_top hαpos hαL htop).1)
  · exact .inr (hU.three_support_lower_of_top hαpos hαL htop).2.2

/-- Every actual joint cap maximizer has terminal angle beyond the
initial interval. Recentring and canonicalization preserve its own angle
and maximizing score before the proved top-endpoint bound is applied. -/
theorem IsJointCapMaximizer.terminal_angle_gt_arctan_eight_thirds
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α) :
    Real.arctan (8 / 3) < α := by
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
  by_contra! hα1
  linarith [hV.reference_le, initialAngle_rational_lt_half_M,
    hV.isCap.capScore_lt_initialAngle_rational_of_top_endpoint
      (div_nonneg hU.isCap.capWidth_nonneg (by norm_num)) hleft hright hV.angle_mem.1 hα1 htop]

end AmbidextrousSofa
