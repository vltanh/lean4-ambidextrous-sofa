module

public import AmbidextrousSofa.Analysis.LowHeightGeometry

@[expose] public section

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
    IntervalIntegrable (partialBarrier U α) volume a b :=
  (integrableOn_partialBarrier_Icc hU.isCompact hα0 hα (min a b) (max a b)).intervalIntegrable

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
  have hproj := horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex
  rw [hleft, hright] at hproj
  calc (∫ x in C..(2 * C), capRoof U x) ≤ ∫ x in C..(2 * C), 1 - max (1 - 2 * C - u + x) 0 :=
        intervalIntegral.integral_mono_on (by linarith) (hU.intervalIntegrable_capRoof _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _) fun x hx => by
            have := hU.capRoof_le_diagonalRight (hproj ▸ Icc_subset_Icc (by linarith) le_rfl hx)
            rw [le_sub_comm]
            exact max_le (by linarith) (by linarith [capRoof_le_one hU.isCompact hU.inStrip x])
    _ = C - (1 - u) ^ 2 / 2 := by
        rw [intervalIntegral.integral_sub intervalIntegrable_const
          (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_const,
          integral_positive_ramp_add, max_eq_left (by linarith), max_eq_right (by linarith)]
        ring

theorem IsDownwardCap.lowHeight_left_reward_le {U : Set Plane}
    (hU : IsDownwardCap U) {C v : ℝ} (hC : 1 / 2 ≤ C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hdiag : diagonalLeft U = 2 * C + v) (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 4)
    (hceiling : ∀ x ∈ Icc (-2 * C) C, capRoof U x ≤ lowCeiling C x) :
    (∫ x in (-2 * C)..(-C), capRoof U x) ≤ 3 * C / 8 - (1 / 4 - v) ^ 2 / 2 := by
  have hC0 : 0 < C := by linarith
  have hproj := horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex
  rw [hleft, hright] at hproj
  calc (∫ x in (-2 * C)..(-C), capRoof U x)
      ≤ ∫ x in (-2 * C)..(-C), lowCeiling C x - max (1 / 4 - v - 2 * C - x) 0 :=
        intervalIntegral.integral_mono_on (by linarith) (hU.intervalIntegrable_capRoof _ _)
          (((continuous_lowCeiling C).sub (by fun_prop)).intervalIntegrable _ _) fun x hx => by
            have := hU.capRoof_le_diagonalLeft (hproj ▸ Icc_subset_Icc le_rfl (by linarith) hx)
            have := lowCeiling_eq_quarter_add hC0.ne' x
            have : 0 ≤ (x + 2 * C) / (4 * C) := div_nonneg (by linarith [hx.1]) (by positivity)
            rw [le_sub_comm]
            exact max_le (by linarith) (by linarith [hceiling x ⟨hx.1, by linarith [hx.2]⟩])
    _ = 3 * C / 8 - (1 / 4 - v) ^ 2 / 2 := by
        rw [intervalIntegral.integral_sub ((continuous_lowCeiling C).intervalIntegrable _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _), integral_lowCeiling_left hC0,
          integral_positive_ramp_sub, max_eq_left (by linarith), max_eq_right (by linarith)]
        ring

theorem IsDownwardCap.lowHeight_refined_reward_le {U : Set Plane}
    (hU : IsDownwardCap U) {C : ℝ} (hC : 1 / 2 ≤ C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hhigh : capRoof U C = 1)
    (hceiling : ∀ x ∈ Icc (-2 * C) C, capRoof U x ≤ lowCeiling C x) :
    (∫ x in (-2 * C)..(-C), capRoof U x) + (∫ x in C..(2 * C), capRoof U x) ≤
      11 * C / 8 - (1 - (diagonalRight U - 2 * C)) ^ 2 / 2 -
        (1 / 4 - (diagonalLeft U - 2 * C)) ^ 2 / 2 := by
  obtain ⟨-, huC, hu1, hv0, hv1⟩ :=
    hU.lowHeight_diagonal_excess_bounds hC hleft hright hhigh hceiling
  linarith [hU.lowHeight_right_reward_le (by linarith) hleft hright (by ring) hu1 huC,
    hU.lowHeight_left_reward_le hC hleft hright (by ring) hv0 hv1 hceiling]

/-- A tent of height `h` with apex `d ∈ [-C, C]` below the barrier bounds its middle
integral from below. -/
private theorem IsDownwardCap.tent_le_integral_partialBarrier {U : Set Plane}
    (hU : IsDownwardCap U) {C d h α : ℝ} (hd : d ∈ Icc (-C) C) (hα0 : Real.pi / 4 ≤ α)
    (hαL : α ≤ Real.pi / 2) (htent : ∀ x, h - |x - d| ≤ partialBarrier U α x) :
    (max h 0) ^ 2 - (max (h - C - d) 0) ^ 2 / 2 - (max (h - C + d) 0) ^ 2 / 2 ≤
      ∫ x in (-C)..C, partialBarrier U α x :=
  integral_positive_tent_centered hd h ▸ intervalIntegral.integral_mono_on (hd.1.trans hd.2)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (hU.intervalIntegrable_partialBarrier (by linarith [Real.pi_pos]) hαL _ _)
    fun x _ => max_le (htent x) (partialBarrier_nonneg _ _ _)

theorem IsDownwardCap.lowHeight_middle_niche_lower {U : Set Plane}
    (hU : IsDownwardCap U) {C u v α : ℝ} (hC : 1 / 2 ≤ C) (hCmax : C ≤ 23 / 20)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 4)
    (hR : diagonalRight U = 2 * C + u) (hL : diagonalLeft U = 2 * C + v)
    (hα0 : Real.pi / 4 ≤ α) (hαL : α ≤ Real.pi / 2) :
    (max (2 * C + (u + v) / 2 - Real.sqrt 2) 0) ^ 2 -
      (max (C + u - Real.sqrt 2) 0) ^ 2 / 2 ≤ ∫ x in (-C)..C, partialBarrier U α x := by
  have := hU.tent_le_integral_partialBarrier (C := C) (h := 2 * C + (u + v) / 2 - Real.sqrt 2)
    (d := (u - v) / 2) ⟨by linarith, by linarith⟩ hα0 hαL fun x => by
      have := (le_max_left _ _).trans (hU.diagonal_tent_le_partialBarrier hα0 hαL x)
      rw [hR, hL, show (2 * C + u - (2 * C + v)) / 2 = (u - v) / 2 by ring] at this
      linarith
  rw [max_eq_right (a := 2 * C + (u + v) / 2 - Real.sqrt 2 - C - (u - v) / 2)
      (by linarith [lowHeight_sqrt_bounds.1]),
    show 2 * C + (u + v) / 2 - Real.sqrt 2 - C + (u - v) / 2 = C + u - Real.sqrt 2 by ring] at this
  linarith

/-- The strict low-height exclusion is a theorem about the actual cap and
its entire actual barrier, for every terminal range reaching pi/4. -/
theorem IsDownwardCap.capScore_lt_lowHeightBound_of_affine_middle
    {U : Set Plane} (hU : IsDownwardCap U) {C α : ℝ} (hC : 0 < C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hlow : capRoof U (-C) ≤ 1 / 2) (hhigh : capRoof U C = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c)
    (hα0 : Real.pi / 4 ≤ α) (hαL : α ≤ Real.pi / 2) :
    capScore U α < lowHeightBound := by
  have hceiling := hU.capRoof_le_lowCeiling_of_affine_middle hC hleft hright hlow hhigh haffine
  have hscore := capScore_centered_quarters hU hleft hright α
  have hreward := hU.lowHeight_reward_le hC hceiling
  rcases le_or_gt C (1 / 2) with hsmall | hsmall
  · linarith [lowHeight_small_width_bound hsmall,
      intervalIntegral.integral_nonneg_of_forall (μ := volume) (by linarith : -C ≤ C)
        (partialBarrier_nonneg U α)]
  rcases le_or_gt C (23 / 20) with hmiddle | hlarge
  · obtain ⟨hu0, -, hu1, hv0, hv1⟩ :=
      hU.lowHeight_diagonal_excess_bounds hsmall.le hleft hright hhigh hceiling
    have := lowHeight_surrogate_bound hsmall.le hu1 hv0
    unfold lowHeightSurrogate at this
    linarith [hU.lowHeight_refined_reward_le hsmall.le hleft hright hhigh hceiling,
      hU.lowHeight_middle_niche_lower hsmall.le hmiddle hu0 hu1 hv0 hv1 (by ring) (by ring) hα0
        hαL]
  have ht := hU.tent_le_integral_partialBarrier (C := C) (h := 2 * C - Real.sqrt 2) (d := 0)
    ⟨by linarith, by linarith⟩ hα0 hαL fun x => by
      have := hU.baseline_tent_le_partialBarrier hα0 hαL x
      rw [hleft, hright] at this
      rcases min_le_iff.mp this with h | h <;> linarith [le_abs_self (x - 0), neg_abs_le (x - 0)]
  rw [max_eq_left (by linarith [lowHeight_sqrt_bounds.2.2]), sub_zero, add_zero,
    show 2 * C - Real.sqrt 2 - C = C - Real.sqrt 2 by ring] at ht
  rcases le_or_gt C (Real.sqrt 2) with hclip | hclip
  · rw [max_eq_right (sub_nonpos.mpr hclip)] at ht
    linarith [lowHeight_large_width_unclipped_bound hlarge.le]
  · rw [max_eq_left (sub_nonneg.mpr hclip.le)] at ht
    linarith [lowHeight_large_width_clipped_bound hclip.le]

end AmbidextrousSofa
