module

public import AmbidextrousSofa.Analysis.LowHeightScore
public import AmbidextrousSofa.Analysis.CapTranslation
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
# An actual terminal-wall bound at every proper angle

The right exterior roof lies below the actual first support line. On the
left half of the middle interval, the entire outgoing first wall is a
lower bound for the actual barrier. Their support-height terms cancel
after integration. The other middle half contributes nonnegative cost.

This gives a quadratic bound in the actual quarter-width. Completing its
square yields a bound depending only on the proper terminal angle, for
every downward cap.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem terminal_sin_cos_pos {α : ℝ} (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    0 < Real.sin α ∧ 0 < Real.cos α :=
  ⟨Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [Real.pi_pos]),
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαL⟩⟩

theorem intervalIntegral_const_sub_mul (H k a b : ℝ) :
    (∫ x in a..b, H - k * x) = (b - a) * H - k * (b ^ 2 - a ^ 2) / 2 := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    ((show Continuous (fun x : ℝ => k * x) by fun_prop).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id, smul_eq_mul]
  ring

theorem IsDownwardCap.capRoof_le_first_support_line {U : Set Plane}
    (hU : IsDownwardCap U) {α x : ℝ} (hs : 0 < Real.sin α)
    (hx : x ∈ horizontalProjection U) :
    capRoof U x ≤ support U (unitNormal α) / Real.sin α -
      (Real.cos α / Real.sin α) * x := by
  have : x * Real.cos α + capRoof U x * Real.sin α ≤ support U (unitNormal α) :=
    coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact hx) (unitNormal α)
  rw [div_mul_eq_mul_div, div_sub_div_same, le_div_iff₀ hs]
  linarith

/-- The support height cancels between one charged exterior wing and the
true terminal-wall cost on one half of the middle window. -/
theorem IsDownwardCap.capScore_le_terminal_quadratic_centered {U : Set Plane}
    (hU : IsDownwardCap U) {C α : ℝ} (hC : 0 ≤ C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    capScore U α ≤ (1 + 1 / Real.sin α) * C -
      2 * (Real.cos α / Real.sin α) * C ^ 2 := by
  have hs := (terminal_sin_cos_pos hα0 hαL).1
  have hB := hU.intervalIntegrable_partialBarrier hα0 hαL.le
  have hproj : horizontalProjection U = Icc (-2 * C) (2 * C) := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hleft, hright]
  have hl := intervalIntegral.integral_mono_on (by linarith : -2 * C ≤ -C)
    (hU.intervalIntegrable_capRoof _ _) intervalIntegrable_const
    fun x _ => capRoof_le_one hU.isCompact hU.inStrip x
  have hr := intervalIntegral.integral_mono_on (by linarith : C ≤ 2 * C)
    (hU.intervalIntegrable_capRoof _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)
    fun x hx => hU.capRoof_le_first_support_line hs (hproj ▸ ⟨by linarith [hx.1], hx.2⟩)
  have hm := intervalIntegral.integral_mono_on (by linarith : -C ≤ (0 : ℝ))
    (Continuous.intervalIntegrable (by fun_prop) _ _) (hB _ _) fun x _ =>
    (show support U (unitNormal α) / Real.sin α - 1 / Real.sin α -
      Real.cos α / Real.sin α * x = firstWall U α x by rw [firstWall]; ring).trans_le
      (le_max_right _ _)
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hl
  rw [intervalIntegral_const_sub_mul] at hr hm
  linarith [capScore_centered_quarters hU hleft hright α,
    intervalIntegral.integral_add_adjacent_intervals (hB (-C) 0) (hB 0 C),
    intervalIntegral.integral_nonneg_of_forall (μ := volume) hC (partialBarrier_nonneg U α)]

/-- This all-cap bound retains the entire true outgoing first wall. -/
theorem IsDownwardCap.capScore_le_terminal_bound {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    capScore U α ≤ (1 + 1 / Real.sin α) ^ 2 /
      (8 * (Real.cos α / Real.sin α)) := by
  obtain ⟨hs, hc⟩ := terminal_sin_cos_pos hα0 hαL
  have hk := div_pos hc hs
  have h := hU.centeredCap.capScore_le_terminal_quadratic_centered (C := capWidth U / 4)
    (by linarith [hU.capWidth_nonneg]) (by rw [horizontalLeft_centeredCap hU]; ring)
    (by rw [horizontalRight_centeredCap hU]; ring) hα0 hαL
  rw [capScore_centeredCap hU] at h
  refine h.trans ((le_div_iff₀ (by linarith)).2 ?_)
  linarith [sq_nonneg (4 * (Real.cos α / Real.sin α) * (capWidth U / 4) - (1 + 1 / Real.sin α))]

end AmbidextrousSofa
