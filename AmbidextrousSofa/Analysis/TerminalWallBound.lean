import AmbidextrousSofa.Analysis.LowHeightScore
import AmbidextrousSofa.Analysis.CapTranslation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# An actual terminal-wall bound at every proper angle

The right exterior roof lies below the actual first support line. On the
left half of the middle interval, the entire outgoing first wall is a
lower bound for the actual barrier. Their support-height terms cancel
after integration. The other middle half contributes nonnegative cost.

This gives a quadratic bound in the actual quarter-width. Completing its
square yields a bound depending only on the proper terminal angle. The
argument includes zero-width caps and makes no smoothness, maximality,
symmetry or nonempty-survivor assumption.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem intervalIntegral_const_sub_mul (H k a b : ℝ) :
    (∫ x in a..b, H - k * x) = (b - a) * H - k * (b ^ 2 - a ^ 2) / 2 := by
  rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
    ((continuous_const.mul continuous_id).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_id]
  simp only [smul_eq_mul]
  ring

theorem IsDownwardCap.capRoof_le_first_support_line {U : Set Plane}
    (hU : IsDownwardCap U) {α x : ℝ} (hs : 0 < Real.sin α)
    (hx : x ∈ horizontalProjection U) :
    capRoof U x ≤ support U (unitNormal α) / Real.sin α -
      (Real.cos α / Real.sin α) * x := by
  have hsupport := coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact hx)
    (unitNormal α)
  change x * Real.cos α + capRoof U x * Real.sin α ≤ _ at hsupport
  calc
    capRoof U x ≤ (support U (unitNormal α) - x * Real.cos α) / Real.sin α :=
      (le_div_iff₀ hs).mpr (by linarith)
    _ = _ := by ring

/-- The support height cancels between one charged exterior wing and the
true terminal-wall cost on one half of the middle window. -/
theorem IsDownwardCap.capScore_le_terminal_quadratic_centered {U : Set Plane}
    (hU : IsDownwardCap U) {C α : ℝ} (hC : 0 ≤ C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    capScore U α ≤ (1 + 1 / Real.sin α) * C -
      2 * (Real.cos α / Real.sin α) * C ^ 2 := by
  let H := support U (unitNormal α) / Real.sin α
  let k := Real.cos α / Real.sin α
  let d := 1 / Real.sin α
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0
    (by linarith [hαL, Real.pi_pos])
  have hleftInt : (∫ x in (-2 * C)..(-C), capRoof U x) ≤ C := by
    have h := intervalIntegral.integral_mono_on (by linarith : -2 * C ≤ -C)
      (hU.intervalIntegrable_capRoof (-2 * C) (-C))
      (continuous_const.intervalIntegrable (-2 * C) (-C))
      (fun x _ => capRoof_le_one hU.isCompact hU.inStrip x)
    rw [intervalIntegral.integral_const] at h
    simpa only [smul_eq_mul, mul_one, show -C - -2 * C = C by ring] using h
  have hrightInt : (∫ x in C..(2 * C), capRoof U x) ≤ H * C - 3 * k * C ^ 2 / 2 := by
    have hpoint : ∀ x ∈ Icc C (2 * C), capRoof U x ≤ H - k * x := by
      intro x hx
      apply hU.capRoof_le_first_support_line hs
      rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hleft, hright]
      exact ⟨by linarith [hx.1], hx.2⟩
    have h := intervalIntegral.integral_mono_on (by linarith : C ≤ 2 * C)
      (hU.intervalIntegrable_capRoof C (2 * C))
      ((show Continuous (fun x : ℝ => H - k * x) by fun_prop).intervalIntegrable C (2 * C))
      hpoint
    rw [intervalIntegral_const_sub_mul] at h
    convert h using 1 <;> ring
  have hterminal : ∀ x : ℝ, H - d - k * x ≤ partialBarrier U α x := by
    intro x
    calc
      H - d - k * x = firstWall U α x := by dsimp [H, d, k, firstWall]; ring
      _ ≤ partialBarrier U α x := le_max_right _ _
  have hmiddleLeft : (H - d) * C + k * C ^ 2 / 2 ≤
      ∫ x in (-C)..0, partialBarrier U α x := by
    have h := intervalIntegral.integral_mono_on (by linarith : -C ≤ (0 : ℝ))
      ((show Continuous (fun x : ℝ => (H - d) - k * x) by fun_prop).intervalIntegrable (-C) 0)
      (hU.intervalIntegrable_partialBarrier hα0 hαL.le (-C) 0)
      (fun x _ => hterminal x)
    rw [intervalIntegral_const_sub_mul] at h
    convert h using 1 <;> ring
  have hmiddleRight : 0 ≤ ∫ x in (0 : ℝ)..C, partialBarrier U α x :=
    intervalIntegral.integral_nonneg_of_forall hC (partialBarrier_nonneg U α)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hU.intervalIntegrable_partialBarrier hα0 hαL.le (-C) 0)
    (hU.intervalIntegrable_partialBarrier hα0 hαL.le 0 C)
  have hscore := capScore_centered_quarters hU hleft hright α
  change capScore U α ≤ (1 + d) * C - 2 * k * C ^ 2
  nlinarith

theorem IsDownwardCap.capScore_le_terminal_quadratic {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    capScore U α ≤ (1 + 1 / Real.sin α) * (capWidth U / 4) -
      2 * (Real.cos α / Real.sin α) * (capWidth U / 4) ^ 2 := by
  let C := capWidth U / 4
  have hC : 0 ≤ C := div_nonneg hU.capWidth_nonneg (by norm_num)
  have hleft : horizontalLeft (centeredCap U) = -2 * C := by
    rw [horizontalLeft_centeredCap hU]
    dsimp [C]
    ring
  have hright : horizontalRight (centeredCap U) = 2 * C := by
    rw [horizontalRight_centeredCap hU]
    dsimp [C]
    ring
  have h := hU.centeredCap.capScore_le_terminal_quadratic_centered hC hleft hright hα0 hαL
  rwa [capScore_centeredCap hU] at h

theorem terminal_quadratic_le {b k C : ℝ} (hk : 0 < k) :
    b * C - 2 * k * C ^ 2 ≤ b ^ 2 / (8 * k) := by
  apply (le_div_iff₀ (by positivity : 0 < 8 * k)).mpr
  nlinarith [sq_nonneg (4 * k * C - b)]

/-- This all-cap bound retains the entire true outgoing first wall. -/
theorem IsDownwardCap.capScore_le_terminal_bound {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    capScore U α ≤ (1 + 1 / Real.sin α) ^ 2 /
      (8 * (Real.cos α / Real.sin α)) := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0
    (by linarith [hαL, Real.pi_pos])
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hαL⟩
  exact (hU.capScore_le_terminal_quadratic hα0 hαL).trans
    (terminal_quadratic_le (div_pos hc hs))

end AmbidextrousSofa
