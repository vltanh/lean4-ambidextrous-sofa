module

public import AmbidextrousSofa.Analysis.InitialAngleRaise
public import AmbidextrousSofa.Analysis.DiagonalScalar

@[expose] public section

/-!
# The all-width three-support scalar bound

The diagonal relaxation excludes widths below its own offset `K`. At every remaining width,
the two direct calibration regions and the strict complementary bound
cover the high-left parameter domain. The finite high-right comparison
then gives the same bound under either actual top-endpoint alternative.

Every hypothesis below is a scalar width, trigonometric identity, or
ordinary support compatibility inequality. No optimization conclusion is
provided as an input.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem initialAngleRelaxation_zero (K C d u v b : ℝ) :
    initialAngleRelaxation K C 0 d u v b =
      2 * C - initialAngleRampLoss C v - initialAngleRampLoss C u -
        ∫ x in (-C)..C, max 0 (min (u - K - x) (v - K + x)) := by
  have hQ : initialAngleRightLoss C 0 u b = initialAngleRampLoss C u :=
    intervalIntegral.integral_congr fun x _ => by
      rw [zero_mul, max_eq_left (le_max_left 0 _), max_comm]
  have hN : initialAngleNicheLoss K C 0 d u v b =
      ∫ x in (-C)..C, max 0 (min (u - K - x) (v - K + x)) :=
    intervalIntegral.integral_congr fun x _ => by simp only [zero_mul, le_max_left, max_eq_left]
  rw [initialAngleRelaxation, hQ, hN]

theorem initialAngleRelaxation_le_diagonal {C : ℝ} (hC : 0 ≤ C)
    (K k d u v b : ℝ) :
    initialAngleRelaxation K C k d u v b ≤ initialAngleRelaxation K C 0 0 u v 0 := by
  rw [initialAngleRelaxation_zero, initialAngleRelaxation]
  linarith [initialAngleRampLoss_le_rightLoss hC k u b,
    initialAngle_diagonal_integral_le_nicheLoss hC K k d u v b]

/-- Only the diagonal relaxation is reflected here. -/
theorem initialAngleRelaxation_diagonal_symm (K C u v : ℝ) :
    initialAngleRelaxation K C 0 0 u v 0 = initialAngleRelaxation K C 0 0 v u 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -C) (b := C)
    (fun x : ℝ => max 0 (min (v - K - x) (u - K + x)))
  simp only [neg_neg, sub_neg_eq_add, ← sub_eq_add_neg] at h
  rw [initialAngleRelaxation_zero, initialAngleRelaxation_zero, ← h]
  simp only [min_comm]
  ring

theorem initialAngleRelaxation_diagonal_eq {K C u v : ℝ}
    (hu0 : C ≤ u) (hu1 : u ≤ 2 * C) (hv0 : C ≤ v) (hv1 : v ≤ 2 * C) :
    initialAngleRelaxation K C 0 0 u v 0 = diagonalRelaxation (2 * C) 0 K u v := by
  have h := integral_tilted_diagonal_tent (a := 2 * C) (h := 0) (u := u) (v := v) K
    (by constructor <;> linarith)
  simp only [sub_zero, show -(2 * C) / 2 = -C by ring, show (2 * C) / 2 = C by ring] at h
  rw [initialAngleRelaxation_zero, initialAngleRampLoss_eq_square hu0 hu1,
    initialAngleRampLoss_eq_square hv0 hv1, intervalIntegral.integral_congr
      (g := fun x => max (min (u - K - x) (v - K + x)) 0) fun x _ => max_comm _ _, h,
    diagonalRelaxation]
  ring_nf

/-- A clipped diagonal tent is controlled by its balanced value or the
two bad-apex bounds. No fitted width threshold enters this comparison. -/
theorem initialAngleRelaxation_diagonal_le_max {C u v : ℝ}
    (hC0 : 0 ≤ C)
    (hu1 : u ≤ 2 * C) (hv0 : C ≤ v) (hv1 : v ≤ 2 * C) :
    initialAngleRelaxation (Real.sqrt 2 - 1) C 0 0 u v 0 ≤
      max (2 / 3) (2 * C - 2 * (C - (Real.sqrt 2 - 1) / 2) ^ 2) := by
  have hlow := le_max_left (2 / 3 : ℝ) (2 * C - 2 * (C - (Real.sqrt 2 - 1) / 2) ^ 2)
  have hbalanced := le_max_right (2 / 3 : ℝ) (2 * C - 2 * (C - (Real.sqrt 2 - 1) / 2) ^ 2)
  obtain ⟨hK0, -, hK1⟩ := sqrt_two_sub_one_bounds
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  have hK := sqrt_two_sub_one_quadratic
  generalize Real.sqrt 2 - 1 = K at *
  rcases lt_or_ge (2 * C) K with hK2 | hK2
  · linarith [hlow, initialAngleRelaxation_le_twice_width hC0 K 0 0 u v 0]
  rcases le_total C u with hu0 | hu0
  · rw [initialAngleRelaxation_diagonal_eq hu0 hu1 hv0 hv1]
    linarith [hbalanced, diagonalRelaxation_le_critical (2 * C) 0 K u v (by linarith) (by linarith)
      (by linarith)]
  rcases le_total (u + v) (2 * K) with hsum | hsum
  · linarith [hlow, initialAngleRelaxation_le_two_thirds_of_low_apex hC0 (by linarith) (by linarith)
      hK hv0 hv1 hsum 0 0 0]
  rcases le_total (u - v) (-2 * C) with hapex | hapex
  · linarith [hlow, initialAngleRelaxation_le_two_thirds_of_left_apex hC0 hv0 hv1 hapex K 0 0 0]
  have hfirst := initialAngleRelaxation_first_region_le (k := 0) (d := 0) (b := u) (by linarith)
    hK2 le_rfl (by norm_num) le_rfl hv0 hv1 hsum (by constructor <;> linarith) (by linarith)
  rw [initialAngleRelaxation_zero] at hfirst ⊢
  unfold initialAngleStationaryValue at hfirst
  linarith [hbalanced, sq_nonneg (u + v - 2 * C - K)]


/-- The quantitative width needed by the terminal corner is excluded
by the diagonal comparison, independently of the terminal slope. -/
theorem initialAngleRelaxation_diagonal_corner_width {C u v : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ initialAngleCornerWidth)
    (hu1 : u ≤ 2 * C) (hv0 : C ≤ v) (hv1 : v ≤ 2 * C) :
    initialAngleRelaxation (Real.sqrt 2 - 1) C 0 0 u v 0 < referenceHalfAreaLower :=
  (initialAngleRelaxation_diagonal_le_max hC0 hu1 hv0 hv1).trans_lt
    (max_lt (by norm_num [referenceHalfAreaLower, referenceRootLower, cubicBracketLower,
      cubicBracketUpper, cubic]) (initialAngle_diagonal_corner_width hC1))

/-- The initial-angle proof needs only the intrinsic diagonal width `K`. -/
theorem initialAngleRelaxation_natural_width {C u v : ℝ}
    (hC0 : 0 ≤ C) (hCK : C ≤ Real.sqrt 2 - 1) (hu1 : u ≤ 2 * C) (hv1 : v ≤ 2 * C)
    (hhigh : C ≤ v ∨ C ≤ u) (k d b : ℝ) :
    initialAngleRelaxation (Real.sqrt 2 - 1) C k d u v b < (3 / 4 : ℝ) := by
  apply (initialAngleRelaxation_le_diagonal hC0 (Real.sqrt 2 - 1) k d u v b).trans_lt
  have hmax := max_lt (by norm_num : (2 / 3 : ℝ) < 3 / 4)
    (initialAngle_diagonal_natural_width hCK)
  rcases hhigh with hv0 | hu0
  · exact (initialAngleRelaxation_diagonal_le_max hC0 hu1 hv0 hv1).trans_lt hmax
  · rw [initialAngleRelaxation_diagonal_symm]
    exact (initialAngleRelaxation_diagonal_le_max hC0 hv1 hu0 hu1).trans_lt hmax

theorem initialAngleRelaxation_corner_width {C u v : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ initialAngleCornerWidth) (hu1 : u ≤ 2 * C) (hv1 : v ≤ 2 * C)
    (hhigh : C ≤ v ∨ C ≤ u) (k d b : ℝ) :
    initialAngleRelaxation (Real.sqrt 2 - 1) C k d u v b < referenceHalfAreaLower := by
  apply (initialAngleRelaxation_le_diagonal hC0 (Real.sqrt 2 - 1) k d u v b).trans_lt
  rcases hhigh with hv0 | hu0
  · exact initialAngleRelaxation_diagonal_corner_width hC0 hC1 hu1 hv0 hv1
  · rw [initialAngleRelaxation_diagonal_symm]
    exact initialAngleRelaxation_diagonal_corner_width hC0 hC1 hv1 hu0 hu1

/-- The two fixed-wall calibrations, the two bad apices, and the
geometric complementary tent gap cover the entire high-left parameter domain. -/
theorem initialAngleRelaxation_left_domain_lt {C k d s u v b : ℝ}
    (hKC : Real.sqrt 2 - 1 ≤ C) (hk0 : 3 / 8 ≤ k) (hk1 : k ≤ 4 / 5)
    (hs0 : 0 ≤ s) (hs2 : s ^ 2 = 1 + k ^ 2) (hkd : k * d = s - 1)
    (hbu : b ≤ u) (hu1 : u ≤ 2 * C) (hv0 : C ≤ v) (hv1 : v ≤ 2 * C)
    (hb1 : b ≤ 2 * C) (hcompat : u ≤ 2 * (1 - k) * C + k * b) :
    initialAngleRelaxation (Real.sqrt 2 - 1) C k d u v b < M / 2 := by
  obtain ⟨hK0, -, hK1⟩ := sqrt_two_sub_one_bounds
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  obtain ⟨hdpos, hdK⟩ := initialAngle_inset_bounds (by linarith) (by linarith) hs0 hs2 hkd
  have hreference : (3 / 4 : ℝ) < M / 2 :=
    (by norm_num [referenceHalfAreaLower, referenceRootLower, cubicBracketLower,
      cubicBracketUpper, cubic] : (3 / 4 : ℝ) < referenceHalfAreaLower).trans
        referenceHalfAreaLower_lt_half_M
  have hstation := initialAngle_stationary_lt_half_M (C := C) hk0 hk1 hs0 hs2 hkd
  rcases le_total (u + v) (2 * (Real.sqrt 2 - 1)) with hsum | hsum
  · linarith [initialAngleRelaxation_le_two_thirds_of_low_apex (by linarith) (by linarith)
      (by linarith) sqrt_two_sub_one_quadratic hv0 hv1 hsum k d b]
  rcases le_total (u - v) (-2 * C) with hapex | hapex
  · linarith [initialAngleRelaxation_le_two_thirds_of_left_apex (by linarith) hv0 hv1 hapex
      (Real.sqrt 2 - 1) k d b]
  rcases le_or_gt u (C + (Real.sqrt 2 - 1)) with hu | hu
  · linarith [sq_nonneg (u + v - 2 * C - (Real.sqrt 2 - 1)),
      initialAngleRelaxation_first_region_le (k := k) (d := d) (by linarith) (by linarith)
        (by linarith) (by linarith) hbu hv0 hv1 hsum (by constructor <;> linarith) hu]
  rcases le_or_gt 0 ((1 + k) * C + (Real.sqrt 2 - 1) - v + k * (b - d)) with hY | hY
  · exact (initialAngleRelaxation_second_region_le (by linarith) hKC (by linarith) (by linarith)
      hdpos.le (by linarith) hbu hu.le hu1 hv0 hv1 hb1 hcompat hY).trans_lt hstation
  · exact (initialAngleRelaxation_complement_lt hKC hk0 hk1 hs0 hs2 hkd hu1 hv1
      hcompat hu hY).trans initialAngleComplementScore_lt_half_M

/-- The finite-support estimate holds at every nonnegative width under
the ordinary support compatibility and either high-endpoint alternative. -/
theorem initialAngleRelaxation_all_width_lt {C k d s u v b : ℝ}
    (hC : 0 ≤ C) (hk0 : 3 / 8 ≤ k) (hk1 : k ≤ 4 / 5)
    (hs0 : 0 ≤ s) (hs2 : s ^ 2 = 1 + k ^ 2) (hkd : k * d = s - 1)
    (hbu : b ≤ u) (hu1 : u ≤ 2 * C) (hv1 : v ≤ 2 * C) (hb1 : b ≤ 2 * C)
    (hcompat : u ≤ 2 * (1 - k) * C + k * b) (hhigh : C ≤ v ∨ C ≤ b) :
    initialAngleRelaxation (Real.sqrt 2 - 1) C k d u v b < M / 2 := by
  rcases le_or_gt C (Real.sqrt 2 - 1) with hsmall | hsmall
  · exact (initialAngleRelaxation_natural_width hC hsmall hu1 hv1
      (hhigh.imp_right fun hb => hb.trans hbu) k d b).trans
        ((by norm_num [referenceHalfAreaLower, referenceRootLower, cubicBracketLower,
          cubicBracketUpper, cubic] : (3 / 4 : ℝ) < referenceHalfAreaLower).trans
            referenceHalfAreaLower_lt_half_M)
  have hKC : Real.sqrt 2 - 1 ≤ C := hsmall.le
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  rcases le_or_gt C v with hv0 | hv0
  · exact initialAngleRelaxation_left_domain_lt hKC hk0 hk1 hs0 hs2 hkd hbu hu1 hv0 hv1 hb1 hcompat
  obtain ⟨hdpos, hdK⟩ := initialAngle_inset_bounds (by linarith) (by linarith) hs0 hs2 hkd
  exact (initialAngleRelaxation_le_raise_left hC (by linarith) (by linarith)
    (by linarith [mul_nonneg (by linarith : 0 ≤ 1 - k) hdpos.le]) hu1 hv0.le
    (hhigh.resolve_left hv0.not_ge)).trans_lt (initialAngleRelaxation_left_domain_lt hKC hk0 hk1
      hs0 hs2 hkd hbu hu1 le_rfl (by linarith) hb1 hcompat)

end AmbidextrousSofa
