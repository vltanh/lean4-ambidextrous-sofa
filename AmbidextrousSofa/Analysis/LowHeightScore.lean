import AmbidextrousSofa.Analysis.LowHeightGeometry

/-!
# Strict score exclusion for a low middle endpoint

The proof uses two real diagonal supports and the complete two-ray tent at
pi/4. The exterior reward loses two explicitly integrated triangles. Exact
positive-tent integration then supplies the scalar expression bounded in
LowHeightAlgebra. All widths are covered, and the argument also applies to
proper terminal angles reaching pi/4.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem IsDownwardCap.intervalIntegrable_partialBarrier {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) (a b : ℝ) :
    IntervalIntegrable (partialBarrier U α) volume a b := by
  apply intervalIntegrable_iff'.mpr
  simpa only [uIcc] using integrableOn_partialBarrier_Icc hU.isCompact hα0 hα
    (min a b) (max a b)

theorem capScore_centered_quarters {U : Set Plane} (hU : IsDownwardCap U) {C : ℝ}
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C) (α : ℝ) :
    capScore U α = (∫ x in (-2 * C)..(-C), capRoof U x) +
      (∫ x in C..(2 * C), capRoof U x) - ∫ x in (-C)..C, partialBarrier U α x := by
  rw [hU.capScore_eq_intervalSpatialScore, hleft, hright, intervalSpatialScore,
    show -2 * C + (2 * C - -2 * C) / 4 = -C by ring,
    show 2 * C - (2 * C - -2 * C) / 4 = C by ring]

theorem IsDownwardCap.lowHeight_right_reward_le {U : Set Plane}
    (hU : IsDownwardCap U) {C u : ℝ} (hC : 0 < C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hdiag : diagonalRight U = 2 * C + u) (hu1 : u ≤ 1) (huC : 1 - C ≤ u) :
    (∫ x in C..(2 * C), capRoof U x) ≤ C - (1 - u) ^ 2 / 2 := by
  let ramp : ℝ → ℝ := fun x => max (1 - 2 * C - u + x) 0
  have hcont : Continuous ramp := by dsimp [ramp]; fun_prop
  have hpoint : ∀ x ∈ Icc C (2 * C), capRoof U x ≤ 1 - ramp x := by
    intro x hx
    have hxU : x ∈ horizontalProjection U := by
      rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hleft, hright]
      exact ⟨by linarith [hx.1], hx.2⟩
    have hroof := hU.capRoof_le_diagonalRight hxU
    rw [hdiag] at hroof
    have hbound : ramp x ≤ 1 - capRoof U x := max_le
      (by linarith) (sub_nonneg.mpr (capRoof_le_one hU.isCompact hU.inStrip x))
    linarith
  have hmono := intervalIntegral.integral_mono_on (by linarith : C ≤ 2 * C)
    (hU.intervalIntegrable_capRoof C (2 * C))
    ((continuous_const.sub hcont).intervalIntegrable C (2 * C)) hpoint
  have hintegral : (∫ x in C..(2 * C), 1 - ramp x) = C - (1 - u) ^ 2 / 2 := by
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _), intervalIntegral.integral_const]
    dsimp [ramp]
    rw [integral_positive_ramp_add,
      show 1 - 2 * C - u + 2 * C = 1 - u by ring,
      show 1 - 2 * C - u + C = 1 - C - u by ring,
      max_eq_left (sub_nonneg.mpr hu1), max_eq_right (by linarith : 1 - C - u ≤ 0)]
    simp only [smul_eq_mul]
    ring
  exact hintegral ▸ hmono

theorem IsDownwardCap.lowHeight_left_reward_le {U : Set Plane}
    (hU : IsDownwardCap U) {C v : ℝ} (hC : 1 / 2 ≤ C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hdiag : diagonalLeft U = 2 * C + v) (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 4)
    (hceiling : ∀ x ∈ Icc (-2 * C) C, capRoof U x ≤ lowCeiling C x) :
    (∫ x in (-2 * C)..(-C), capRoof U x) ≤ 3 * C / 8 - (1 / 4 - v) ^ 2 / 2 := by
  have hCpos : 0 < C := by linarith
  let ramp : ℝ → ℝ := fun x => max ((1 / 4 - v - 2 * C) - x) 0
  have hcont : Continuous ramp := by dsimp [ramp]; fun_prop
  have hpoint : ∀ x ∈ Icc (-2 * C) (-C), capRoof U x ≤ lowCeiling C x - ramp x := by
    intro x hx
    have hxU : x ∈ horizontalProjection U := by
      rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hleft, hright]
      exact ⟨hx.1, by linarith [hx.2]⟩
    have hroof := hU.capRoof_le_diagonalLeft hxU
    rw [hdiag] at hroof
    have hroofC := hceiling x ⟨hx.1, by linarith [hx.2]⟩
    have hceil0 : 1 / 4 ≤ lowCeiling C x := by
      rw [lowCeiling_eq_quarter_add hCpos.ne']
      have hdiv : 0 ≤ (x + 2 * C) / (4 * C) := div_nonneg (by linarith [hx.1]) (by positivity)
      linarith
    have hbound : ramp x ≤ lowCeiling C x - capRoof U x :=
      max_le (by linarith) (sub_nonneg.mpr hroofC)
    linarith
  have hmono := intervalIntegral.integral_mono_on (by linarith : -2 * C ≤ -C)
    (hU.intervalIntegrable_capRoof (-2 * C) (-C))
    (((continuous_lowCeiling C).sub hcont).intervalIntegrable (-2 * C) (-C)) hpoint
  have hintegral : (∫ x in (-2 * C)..(-C), lowCeiling C x - ramp x) =
      3 * C / 8 - (1 / 4 - v) ^ 2 / 2 := by
    rw [intervalIntegral.integral_sub ((continuous_lowCeiling C).intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _), integral_lowCeiling_left hCpos]
    dsimp [ramp]
    rw [integral_positive_ramp_sub,
      show 1 / 4 - v - 2 * C - -2 * C = 1 / 4 - v by ring,
      show 1 / 4 - v - 2 * C - -C = 1 / 4 - v - C by ring,
      max_eq_left (sub_nonneg.mpr hv1), max_eq_right (by linarith : 1 / 4 - v - C ≤ 0)]
    ring
  exact hintegral ▸ hmono

theorem IsDownwardCap.lowHeight_refined_reward_le {U : Set Plane}
    (hU : IsDownwardCap U) {C : ℝ} (hC : 1 / 2 ≤ C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hhigh : capRoof U C = 1)
    (hceiling : ∀ x ∈ Icc (-2 * C) C, capRoof U x ≤ lowCeiling C x) :
    (∫ x in (-2 * C)..(-C), capRoof U x) + (∫ x in C..(2 * C), capRoof U x) ≤
      11 * C / 8 - (1 - (diagonalRight U - 2 * C)) ^ 2 / 2 -
        (1 / 4 - (diagonalLeft U - 2 * C)) ^ 2 / 2 := by
  obtain ⟨_, huC, hu1, hv0, hv1⟩ := hU.lowHeight_diagonal_excess_bounds hC hleft hright hhigh hceiling
  have hr := hU.lowHeight_right_reward_le (by linarith) hleft hright
    (u := diagonalRight U - 2 * C) (by ring) hu1 huC
  have hl := hU.lowHeight_left_reward_le hC hleft hright
    (v := diagonalLeft U - 2 * C) (by ring) hv0 hv1 hceiling
  linarith

theorem IsDownwardCap.lowHeight_middle_niche_lower {U : Set Plane}
    (hU : IsDownwardCap U) {C u v α : ℝ} (hC : 1 / 2 ≤ C) (hCmax : C ≤ 23 / 20)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 4)
    (hR : diagonalRight U = 2 * C + u) (hL : diagonalLeft U = 2 * C + v)
    (hα0 : Real.pi / 4 ≤ α) (hαL : α ≤ Real.pi / 2) :
    (max (2 * C + (u + v) / 2 - Real.sqrt 2) 0) ^ 2 -
      (max (C + u - Real.sqrt 2) 0) ^ 2 / 2 ≤ ∫ x in (-C)..C, partialBarrier U α x := by
  let h : ℝ := 2 * C + (u + v) / 2 - Real.sqrt 2
  let d : ℝ := (u - v) / 2
  have hd : d ∈ Icc (-C) C := by dsimp [d]; constructor <;> linarith
  have hheight : (diagonalRight U + diagonalLeft U) / 2 - Real.sqrt 2 = h := by
    rw [hR, hL]
    dsimp [h]
    ring
  have hcenter : (diagonalRight U - diagonalLeft U) / 2 = d := by
    rw [hR, hL]
    dsimp [d]
    ring
  have hpoint : ∀ x, max (h - |x - d|) 0 ≤ partialBarrier U α x := by
    intro x
    simpa only [hheight, hcenter] using hU.diagonal_tent_le_partialBarrier hα0 hαL x
  have hc : Continuous (fun x : ℝ => max (h - |x - d|) 0) := by fun_prop
  have hmono := intervalIntegral.integral_mono_on (by linarith : -C ≤ C)
    (hc.intervalIntegrable (-C) C)
    (hU.intervalIntegrable_partialBarrier (by linarith [Real.pi_pos]) hαL (-C) C)
    (fun x _ => hpoint x)
  rw [integral_positive_tent_centered hd] at hmono
  have htail : h - C - d ≤ 0 := by
    dsimp [h, d]
    linarith [lowHeight_sqrt_bounds.1]
  rw [max_eq_right htail, show h - C + d = C + u - Real.sqrt 2 by dsimp [h, d]; ring] at hmono
  simpa only [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, sub_zero] using hmono

theorem IsDownwardCap.baseline_positive_tent_integral_le {U : Set Plane}
    (hU : IsDownwardCap U) {C α : ℝ} (hC : 0 < C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hα0 : Real.pi / 4 ≤ α) (hαL : α ≤ Real.pi / 2) :
    (max (2 * C - Real.sqrt 2) 0) ^ 2 - (max (C - Real.sqrt 2) 0) ^ 2 ≤
      ∫ x in (-C)..C, partialBarrier U α x := by
  have hpoint : ∀ x, max (2 * C - Real.sqrt 2 - |x|) 0 ≤ partialBarrier U α x := by
    intro x
    have h := hU.baseline_tent_le_partialBarrier hα0 hαL x
    rw [hleft, hright] at h
    have heq : min (2 * C - Real.sqrt 2 - x) (x - -2 * C - Real.sqrt 2) =
        2 * C - Real.sqrt 2 - |x| := by
      have ht := min_symmetric_lines (2 * C - Real.sqrt 2) 0 x
      simpa only [add_zero, sub_zero, show x - -2 * C - Real.sqrt 2 =
        (2 * C - Real.sqrt 2) + x by ring] using ht
    rw [heq] at h
    exact max_le h (partialBarrier_nonneg _ _ _)
  have hc : Continuous (fun x : ℝ => max (2 * C - Real.sqrt 2 - |x - 0|) 0) := by fun_prop
  have hmono := intervalIntegral.integral_mono_on (by linarith : -C ≤ C)
    (hc.intervalIntegrable (-C) C)
    (hU.intervalIntegrable_partialBarrier (by linarith [Real.pi_pos]) hαL (-C) C)
    (fun x _ => by simpa only [sub_zero] using hpoint x)
  rw [integral_positive_tent_centered (show (0 : ℝ) ∈ Icc (-C) C by constructor <;> linarith)] at hmono
  simp only [sub_zero, add_zero, show 2 * C - Real.sqrt 2 - C = C - Real.sqrt 2 by ring] at hmono
  linarith

/-- The strict low-height exclusion is a theorem about the actual cap and
its entire actual barrier, for every terminal range reaching pi/4. -/
theorem IsDownwardCap.capScore_lt_lowHeightBound_of_ceiling
    {U : Set Plane} (hU : IsDownwardCap U) {C α : ℝ} (hC : 0 < C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hhigh : capRoof U C = 1)
    (hceiling : ∀ x ∈ Icc (-2 * C) C, capRoof U x ≤ lowCeiling C x)
    (hα0 : Real.pi / 4 ≤ α) (hαL : α ≤ Real.pi / 2) :
    capScore U α < lowHeightBound := by
  have hscore := capScore_centered_quarters hU hleft hright α
  have hreward := hU.lowHeight_reward_le hC hceiling
  by_cases hsmall : C ≤ 1 / 2
  · have hn : 0 ≤ ∫ x in (-C)..C, partialBarrier U α x :=
      intervalIntegral.integral_nonneg_of_forall (by linarith) (partialBarrier_nonneg U α)
    linarith [lowHeight_small_width_bound hsmall]
  have hCmin : 1 / 2 ≤ C := (le_of_not_ge hsmall)
  by_cases hmiddle : C ≤ 23 / 20
  · let u : ℝ := diagonalRight U - 2 * C
    let v : ℝ := diagonalLeft U - 2 * C
    obtain ⟨hu0, _, hu1, hv0, hv1⟩ := hU.lowHeight_diagonal_excess_bounds
      hCmin hleft hright hhigh hceiling
    have hrefined := hU.lowHeight_refined_reward_le hCmin hleft hright hhigh hceiling
    have hniche := hU.lowHeight_middle_niche_lower hCmin hmiddle hu0 hu1 hv0 hv1
      (by dsimp [u]; ring : diagonalRight U = 2 * C + u)
      (by dsimp [v]; ring : diagonalLeft U = 2 * C + v) hα0 hαL
    have hbound : capScore U α ≤ lowHeightSurrogate C u v := by
      unfold lowHeightSurrogate
      change _ ≤ 11 * C / 8 - (1 - u) ^ 2 / 2 - (1 / 4 - v) ^ 2 / 2 -
        (max (2 * C + (u + v) / 2 - Real.sqrt 2) 0) ^ 2 +
          (max (C + u - Real.sqrt 2) 0) ^ 2 / 2
      change _ ≤ 11 * C / 8 - (1 - u) ^ 2 / 2 - (1 / 4 - v) ^ 2 / 2 at hrefined
      linarith
    exact hbound.trans_lt (lowHeight_surrogate_bound hCmin hu1 hv0)
  · have hlarge : 23 / 20 ≤ C := (le_of_not_ge hmiddle)
    have hniche := hU.baseline_positive_tent_integral_le hC hleft hright hα0 hαL
    have hheight : 0 ≤ 2 * C - Real.sqrt 2 := by linarith [lowHeight_sqrt_bounds.2.2]
    rw [max_eq_left hheight] at hniche
    by_cases hclip : C ≤ Real.sqrt 2
    · rw [max_eq_right (sub_nonpos.mpr hclip)] at hniche
      have hbound := lowHeight_large_width_unclipped_bound hlarge
      nlinarith
    · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge hclip))] at hniche
      have hbound := lowHeight_large_width_clipped_bound (le_of_not_ge hclip)
      nlinarith

theorem IsDownwardCap.capScore_lt_lowHeightBound_of_affine_middle
    {U : Set Plane} (hU : IsDownwardCap U) {C α : ℝ} (hC : 0 < C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hlow : capRoof U (-C) ≤ 1 / 2) (hhigh : capRoof U C = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hα0 : Real.pi / 4 ≤ α) (hαL : α ≤ Real.pi / 2) :
    capScore U α < lowHeightBound :=
  hU.capScore_lt_lowHeightBound_of_ceiling hC hleft hright hhigh
    (hU.capRoof_le_lowCeiling_of_affine_middle hC hleft hright hlow hhigh haffine) hα0 hαL

end AmbidextrousSofa
