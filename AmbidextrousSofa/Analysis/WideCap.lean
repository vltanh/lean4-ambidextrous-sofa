module

public import AmbidextrousSofa.Measure.CapScore

@[expose] public section

/-!
# A coercive bound for the actual cap score

Every corner at a visited angle lies below the actual barrier. The two
baseline endpoints supply support witnesses at angle `π / 4`, and their
two attached inner walls give a tent below the actual barrier. The
signed tent integral on the middle half is evaluated exactly. This proves
the large-width exclusion on the full cap domain, including subunit height,
nonsmooth boundaries, and a terminal angle equal to `π / 4`.

This is a compactness reduction; the sharp estimate for intermediate widths is a
separate step.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem IsDownwardCap.left_baseline_mem {U : Set Plane} (hU : IsDownwardCap U) :
    (horizontalLeft U, 0) ∈ U := by
  obtain ⟨p, hp, hpx⟩ := horizontalLeft_mem hU.nonempty hU.isCompact
  exact hpx ▸ hU.baseline_mem hp

theorem IsDownwardCap.right_baseline_mem {U : Set Plane} (hU : IsDownwardCap U) :
    (horizontalRight U, 0) ∈ U := by
  obtain ⟨p, hp, hpx⟩ := horizontalRight_mem hU.nonempty hU.isCompact
  exact hpx ▸ hU.baseline_mem hp

theorem IsDownwardCap.firstWall_pi_div_four_lower {U : Set Plane}
    (hU : IsDownwardCap U) (x : ℝ) :
    horizontalRight U - Real.sqrt 2 - x ≤ firstWall U (Real.pi / 4) x := by
  have hw := coordDot_le_support hU.isCompact hU.right_baseline_mem (unitNormal (Real.pi / 4))
  rw [firstWall]
  simp only [coordDot, unitNormal, Real.cos_pi_div_four, Real.sin_pi_div_four] at hw ⊢
  rw [le_div_iff₀ (by positivity)]
  linarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem IsDownwardCap.secondWall_pi_div_four_lower {U : Set Plane}
    (hU : IsDownwardCap U) (x : ℝ) :
    x - horizontalLeft U - Real.sqrt 2 ≤ secondWall U (Real.pi / 4) x := by
  have hw := coordDot_le_support hU.isCompact hU.left_baseline_mem
    (companionNormal (Real.pi / 4))
  rw [secondWall]
  simp only [coordDot, companionNormal, Real.cos_pi_div_four, Real.sin_pi_div_four] at hw ⊢
  rw [le_div_iff₀ (by positivity)]
  linarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- The corner at a visited angle lies below the barrier. At the terminal angle the corner
uses the actual whole outgoing wall. -/
theorem cornerWall_le_partialBarrier {U : Set Plane} (hU : IsCompact U) {t α : ℝ} (ht0 : 0 < t)
    (htα : t ≤ α) (hαL : α ≤ Real.pi / 2) (x : ℝ) : cornerWall U t x ≤ partialBarrier U α x := by
  rcases htα.lt_or_eq with hlt | rfl
  · exact (cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU hαL x) ⟨ht0, hlt⟩).trans
      (le_max_left _ _)
  · exact (min_le_left _ _).trans (le_max_right _ _)

theorem cornerWall_pi_div_four_le_partialBarrier {U : Set Plane}
    (hU : IsCompact U) {α : ℝ} (hα0 : Real.pi / 4 ≤ α)
    (hαL : α ≤ Real.pi / 2) (x : ℝ) :
    cornerWall U (Real.pi / 4) x ≤ partialBarrier U α x :=
  cornerWall_le_partialBarrier hU (by positivity) hα0 hαL x

/-- Exact integral of the signed tent on the moving middle half. The formula
does not replace negative fibers by their positive part. -/
theorem integral_middleHalf_baseline_tent {l r : ℝ} (hlr : l ≤ r) (d : ℝ) :
    (∫ x in middleHalfInterval l r, min (r - d - x) (x - l - d)) =
      3 * (r - l) ^ 2 / 16 - d * (r - l) / 2 := by
  have hc : Continuous (fun x : ℝ => min (r - d - x) (x - l - d)) := by fun_prop
  have ham : l + (r - l) / 4 ≤ (l + r) / 2 := by linarith
  have hmb : (l + r) / 2 ≤ r - (r - l) / 4 := by linarith
  rw [middleHalfInterval, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (ham.trans hmb),
    ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ ((l + r) / 2))
      (hc.intervalIntegrable _ _),
    intervalIntegral.integral_congr (g := fun x => x - l - d) fun x hx =>
      min_eq_right (by rw [uIcc_of_le ham] at hx; linarith [hx.2]),
    intervalIntegral.integral_congr (g := fun x => r - d - x) fun x hx =>
      min_eq_left (by rw [uIcc_of_le hmb] at hx; linarith [hx.1])]
  simp [intervalIntegral.integral_comp_sub_left (fun x => x)]
  ring

/-- Every cap of width at least six lies strictly below half the reference
constant; no smoothness, symmetry, or full-turn hypothesis is used. -/
theorem IsDownwardCap.capScore_lt_half_M_of_six_le_width {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα0 : Real.pi / 4 ≤ α)
    (hαL : α ≤ Real.pi / 2) (hwidth : 6 ≤ capWidth U) :
    capScore U α < M / 2 := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  rw [capScore_eq_integrals]
  rw [capWidth] at hwidth
  set l := horizontalLeft U
  set r := horizontalRight U
  -- The roof is at most one on the outer half, and the baseline tent lies below the barrier.
  have hroof := setIntegral_mono (s := Icc l r \ middleHalfInterval l r)
    ((hU.integrableOn_capRoof_Icc l r).mono_set sdiff_subset)
    (continuous_const.integrableOn_Icc.mono_set sdiff_subset)
    (fun x => capRoof_le_one hU.isCompact hU.inStrip x)
  rw [setIntegral_const, smul_eq_mul, mul_one, volumeReal_exterior_middleHalfInterval hlr] at hroof
  have hniche := setIntegral_mono (s := middleHalfInterval l r)
    ((show Continuous fun x => min (r - Real.sqrt 2 - x) (x - l - Real.sqrt 2) by
      fun_prop).continuousOn.integrableOn_compact isCompact_Icc)
    ((integrableOn_partialBarrier_Icc hU.isCompact (by linarith [Real.pi_pos]) hαL l r).mono_set
      (middleHalfInterval_subset hlr)) fun x => (min_le_min (hU.firstWall_pi_div_four_lower x)
        (hU.secondWall_pi_div_four_lower x)).trans
          (cornerWall_pi_div_four_le_partialBarrier hU.isCompact hα0 hαL x)
  rw [integral_middleHalf_baseline_tent hlr] at hniche
  have hsqrt : Real.sqrt 2 < 17 / 12 := (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  linarith [one_lt_M, sq_nonneg (r - l - 6),
    mul_pos (sub_pos.mpr hsqrt) (by linarith : (0 : ℝ) < r - l)]

/-- The competitive scalar domain has bounded, nonzero projection width. -/
theorem IsDownwardCap.competitive_width_bounds {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα0 : Real.pi / 4 ≤ α)
    (hαL : α ≤ Real.pi / 2) (hscore : M / 2 ≤ capScore U α) :
    M ≤ capWidth U ∧ capWidth U < 6 :=
  ⟨hU.width_ge_M_of_capScore_ge_half_M hscore, lt_of_not_ge fun h =>
    (hU.capScore_lt_half_M_of_six_le_width hα0 hαL h).not_ge hscore⟩

end AmbidextrousSofa
