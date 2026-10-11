module

public import AmbidextrousSofa.Analysis.LowHeightGeometry

@[expose] public section

/-!
# Exterior rewards below the low-middle-height ceiling

The two real diagonal supports cut a triangle from each charged wing: the
right wing lies below height one and its diagonal support line, the left
wing below the affine ceiling and its diagonal support line. Integrating
these literal bounds gives the refined exterior reward of the low-height
exclusion. The file also splits a centered spatial score into its three
integrals.
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

/-- The spatial score on a projection centered at the origin, as its three integrals. -/
theorem intervalSpatialScore_centered (f n : ℝ → ℝ) (a : ℝ) :
    intervalSpatialScore f n (-a) a = (∫ x in (-a)..(-a / 2), f x) +
      (∫ x in (a / 2)..a, f x) - ∫ x in (-a / 2)..(a / 2), n x := by
  rw [intervalSpatialScore, show -a + (a - -a) / 4 = -a / 2 by ring,
    show a - (a - -a) / 4 = a / 2 by ring]

theorem IsDownwardCap.lowHeight_right_reward_le {U : Set Plane}
    (hU : IsDownwardCap U) {C u : ℝ} (hC : 0 < C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hdiag : diagonalRight U = 2 * C + u) (hu1 : u ≤ 1) (huC : 1 - C ≤ u) :
    (∫ x in C..(2 * C), capRoof U x) ≤ C - (1 - u) ^ 2 / 2 := by
  have hproj := hU.horizontalProjection_eq_of hleft hright
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
  have hproj := hU.horizontalProjection_eq_of hleft hright
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

end AmbidextrousSofa
