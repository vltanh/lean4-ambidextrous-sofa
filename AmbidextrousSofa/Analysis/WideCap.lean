import AmbidextrousSofa.Measure.CapScore

/-!
# A coercive bound for the actual cap score

The two baseline endpoints supply support witnesses at angle `π / 4`.
Their two attached inner walls give a tent below the actual barrier. The
signed tent integral on the middle half is evaluated exactly. This proves
the large-width exclusion on the full cap domain, including subunit height,
nonsmooth boundaries, and a terminal angle equal to `π / 4`.

This is an uncompiled source proof. It is a compactness reduction, not the
remaining sharp estimate on intermediate widths.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem IsDownwardCap.left_baseline_mem {U : Set Plane} (hU : IsDownwardCap U) :
    (horizontalLeft U, 0) ∈ U := by
  obtain ⟨p, hp, hpx⟩ := horizontalLeft_mem hU.nonempty hU.isCompact
  simpa only [hpx] using hU.baseline_mem hp

theorem IsDownwardCap.right_baseline_mem {U : Set Plane} (hU : IsDownwardCap U) :
    (horizontalRight U, 0) ∈ U := by
  obtain ⟨p, hp, hpx⟩ := horizontalRight_mem hU.nonempty hU.isCompact
  simpa only [hpx] using hU.baseline_mem hp

theorem IsDownwardCap.firstWall_pi_div_four_lower {U : Set Plane}
    (hU : IsDownwardCap U) (x : ℝ) :
    horizontalRight U - Real.sqrt 2 - x ≤ firstWall U (Real.pi / 4) x := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsquare : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hw := coordDot_le_support hU.isCompact hU.right_baseline_mem
    (unitNormal (Real.pi / 4))
  simp only [coordDot, unitNormal, Real.cos_pi_div_four, Real.sin_pi_div_four,
    zero_mul, add_zero] at hw
  rw [firstWall, Real.cos_pi_div_four, Real.sin_pi_div_four,
    le_div_iff₀ (by positivity : 0 < Real.sqrt 2 / 2)]
  nlinarith [hsquare]

theorem IsDownwardCap.secondWall_pi_div_four_lower {U : Set Plane}
    (hU : IsDownwardCap U) (x : ℝ) :
    x - horizontalLeft U - Real.sqrt 2 ≤ secondWall U (Real.pi / 4) x := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsquare : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hw := coordDot_le_support hU.isCompact hU.left_baseline_mem
    (companionNormal (Real.pi / 4))
  simp only [coordDot, companionNormal, Real.cos_pi_div_four, Real.sin_pi_div_four,
    zero_mul, add_zero] at hw
  rw [secondWall, Real.cos_pi_div_four, Real.sin_pi_div_four,
    le_div_iff₀ (by positivity : 0 < Real.sqrt 2 / 2)]
  nlinarith [hsquare]

/-- The endpoint case uses the actual whole terminal wall. -/
theorem cornerWall_pi_div_four_le_partialBarrier {U : Set Plane}
    (hU : IsCompact U) {α : ℝ} (hα0 : Real.pi / 4 ≤ α)
    (hαL : α ≤ Real.pi / 2) (x : ℝ) :
    cornerWall U (Real.pi / 4) x ≤ partialBarrier U α x := by
  rcases eq_or_lt_of_le hα0 with rfl | hlt
  · exact (min_le_left _ _).trans (le_max_right _ _)
  · exact (cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU hαL x)
      ⟨by linarith [Real.pi_pos], hlt⟩).trans (le_max_left _ _)

/-- The lower tent is obtained from real support witnesses in the cap. -/
theorem IsDownwardCap.baseline_tent_le_partialBarrier {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα0 : Real.pi / 4 ≤ α)
    (hαL : α ≤ Real.pi / 2) (x : ℝ) :
    min (horizontalRight U - Real.sqrt 2 - x)
      (x - horizontalLeft U - Real.sqrt 2) ≤ partialBarrier U α x := by
  exact (min_le_min (hU.firstWall_pi_div_four_lower x)
    (hU.secondWall_pi_div_four_lower x)).trans
    (cornerWall_pi_div_four_le_partialBarrier hU.isCompact hα0 hαL x)

/-- Exact integral of the signed tent on the moving middle half. The formula
does not replace negative fibers by their positive part. -/
theorem integral_middleHalf_baseline_tent {l r : ℝ} (hlr : l ≤ r) (d : ℝ) :
    (∫ x in middleHalfInterval l r, min (r - d - x) (x - l - d)) =
      3 * (r - l) ^ 2 / 16 - d * (r - l) / 2 := by
  let a := l + (r - l) / 4
  let m := (l + r) / 2
  let b := r - (r - l) / 4
  have ham : a ≤ m := by dsimp [a, m]; linarith
  have hmb : m ≤ b := by dsimp [m, b]; linarith
  have hc : Continuous (fun x : ℝ => min (r - d - x) (x - l - d)) := by
    fun_prop
  have hleft :
      (∫ x in a..m, min (r - d - x) (x - l - d)) =
        ∫ x in a..m, x - l - d := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le ham] at hx
    apply min_eq_right
    dsimp [m] at hx
    linarith [hx.2]
  have hright :
      (∫ x in m..b, min (r - d - x) (x - l - d)) =
        ∫ x in m..b, r - d - x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hmb] at hx
    apply min_eq_left
    dsimp [m] at hx
    linarith [hx.1]
  have hleft_value : (∫ x in a..m, x - l - d) =
      (m ^ 2 - a ^ 2) / 2 - (m - a) * l - (m - a) * d := by
    simp only [intervalIntegral.integral_sub
      ((continuous_id.sub continuous_const).intervalIntegrable a m) intervalIntegrable_const,
      intervalIntegral.integral_sub (continuous_id.intervalIntegrable a m)
        intervalIntegrable_const,
      integral_id, intervalIntegral.integral_const, smul_eq_mul]
  have hright_value : (∫ x in m..b, r - d - x) =
      (b - m) * (r - d) - (b ^ 2 - m ^ 2) / 2 := by
    simp only [intervalIntegral.integral_sub intervalIntegrable_const
      (continuous_id.intervalIntegrable m b),
      intervalIntegral.integral_const, integral_id, smul_eq_mul]
  change (∫ x in Icc a b, min (r - d - x) (x - l - d)) = _
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (ham.trans hmb),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable a m) (hc.intervalIntegrable m b),
    hleft, hright, hleft_value, hright_value]
  dsimp [a, m, b]
  ring

/-- A quadratic upper bound tending to negative infinity with the width. -/
theorem IsDownwardCap.capScore_le_width_quadratic {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα0 : Real.pi / 4 ≤ α)
    (hαL : α ≤ Real.pi / 2) :
    capScore U α ≤ (1 + Real.sqrt 2) * capWidth U / 2 - 3 * capWidth U ^ 2 / 16 := by
  let l := horizontalLeft U
  let r := horizontalRight U
  let I := Icc l r
  let J := middleHalfInterval l r
  have hlr : l ≤ r := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hJ : IsCompact J := isCompact_Icc
  have hRoof : IntegrableOn (capRoof U) (I \ J) :=
    (hU.integrableOn_capRoof_Icc l r).mono_set sdiff_subset
  have hOne : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (I \ J) :=
    (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).mono_set
      sdiff_subset
  have hRoofBound : (∫ x in I \ J, capRoof U x) ≤ capWidth U / 2 := by
    have h := integral_mono hRoof hOne
      (fun x => capRoof_le_one hU.isCompact hU.inStrip x)
    simpa only [setIntegral_const, smul_eq_mul, mul_one,
      volumeReal_exterior_middleHalfInterval hlr, capWidth, I, J, l, r] using h
  have hTent : IntegrableOn (fun x : ℝ => min (r - Real.sqrt 2 - x)
      (x - l - Real.sqrt 2)) J :=
    (show Continuous (fun x : ℝ => min (r - Real.sqrt 2 - x)
      (x - l - Real.sqrt 2)) by fun_prop).continuousOn.integrableOn_compact hJ
  have hBarrier : IntegrableOn (partialBarrier U α) J :=
    (integrableOn_partialBarrier_Icc hU.isCompact
      (by linarith [Real.pi_pos]) hαL l r).mono_set (middleHalfInterval_subset hlr)
  have hNicheBound : 3 * capWidth U ^ 2 / 16 - Real.sqrt 2 * capWidth U / 2 ≤
      ∫ x in J, partialBarrier U α x := by
    have h := integral_mono hTent hBarrier
      (fun x => hU.baseline_tent_le_partialBarrier hα0 hαL x)
    rw [integral_middleHalf_baseline_tent hlr] at h
    exact h
  rw [capScore_eq_integrals]
  change (∫ x in I \ J, capRoof U x) - (∫ x in J, partialBarrier U α x) ≤ _
  nlinarith

/-- Every cap of width at least six lies strictly below half the reference
constant; no smoothness, symmetry, or full-turn hypothesis is used. -/
theorem IsDownwardCap.capScore_lt_half_M_of_six_le_width {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα0 : Real.pi / 4 ≤ α)
    (hαL : α ≤ Real.pi / 2) (hwidth : 6 ≤ capWidth U) :
    capScore U α < M / 2 := by
  have hbound := hU.capScore_le_width_quadratic hα0 hαL
  have hsqrt : Real.sqrt 2 < (17 / 12 : ℝ) :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  have hWpos : 0 < capWidth U := by linarith
  have hstrict := mul_pos (sub_pos.mpr hsqrt) hWpos
  have hhalf : capScore U α < (1 / 2 : ℝ) := by
    nlinarith [sq_nonneg (capWidth U - 6)]
  linarith [one_lt_M]

/-- The competitive scalar domain has bounded, nonzero projection width. -/
theorem IsDownwardCap.competitive_width_bounds {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα0 : Real.pi / 4 ≤ α)
    (hαL : α ≤ Real.pi / 2) (hscore : M / 2 ≤ capScore U α) :
    M ≤ capWidth U ∧ capWidth U < 6 := by
  refine ⟨hU.width_ge_M_of_capScore_ge_half_M hscore, ?_⟩
  by_contra h
  exact (hU.capScore_lt_half_M_of_six_le_width hα0 hαL (le_of_not_gt h)).not_ge hscore

end AmbidextrousSofa
