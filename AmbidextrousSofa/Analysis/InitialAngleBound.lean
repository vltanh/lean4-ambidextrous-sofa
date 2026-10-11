module

public import AmbidextrousSofa.Analysis.InitialAngleRaise
public import AmbidextrousSofa.Analysis.DiagonalScalar

@[expose] public section

/-!
# The all-width three-support scalar bound

The diagonal relaxation excludes small widths. At every remaining width,
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

/-- The high-left diagonal relaxation is below `41/50` at every small
width, including supports below the exterior window and nonpositive apices. -/
theorem initialAngleRelaxation_diagonal_small_width {C u v : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 49 / 100)
    (hu1 : u ≤ 2 * C) (hv0 : C ≤ v) (hv1 : v ≤ 2 * C) :
    initialAngleRelaxation (Real.sqrt 2 - 1) C 0 0 u v 0 < (41 / 50 : ℝ) := by
  have hsmall := initialAngle_diagonal_small_width hC1
  obtain ⟨hK0, hK1⟩ := initialAngle_offset_bounds
  have hK := initialAngle_offset_sq
  generalize Real.sqrt 2 - 1 = K at *
  rcases lt_or_ge (2 * C) K with hK2 | hK2
  · linarith [initialAngleRelaxation_le_twice_width hC0 K 0 0 u v 0]
  rcases le_total C u with hu0 | hu0
  · rw [initialAngleRelaxation_diagonal_eq hu0 hu1 hv0 hv1]
    linarith [diagonalRelaxation_le_critical (2 * C) 0 K u v (by linarith) (by linarith)
      (by linarith)]
  rcases le_total (u + v) (2 * K) with hsum | hsum
  · linarith [initialAngleRelaxation_le_two_thirds_of_low_apex hC0 (by linarith) (by linarith)
      hK hv0 hv1 hsum 0 0 0]
  rcases le_total (u - v) (-2 * C) with hapex | hapex
  · linarith [initialAngleRelaxation_le_two_thirds_of_left_apex hC0 hv0 hv1 hapex K 0 0 0]
  have hfirst := initialAngleRelaxation_first_region_le (k := 0) (d := 0) (b := u) (by linarith)
    hK2 le_rfl (by norm_num) le_rfl hv0 hv1 hsum (by constructor <;> linarith) (by linarith)
  rw [initialAngleRelaxation_zero] at hfirst ⊢
  unfold initialAngleStationaryValue at hfirst
  linarith [sq_nonneg (u + v - 2 * C - K)]

theorem initialAngleRelaxation_small_width {C u v : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 49 / 100) (hu1 : u ≤ 2 * C) (hv1 : v ≤ 2 * C)
    (hhigh : C ≤ v ∨ C ≤ u) (k d b : ℝ) :
    initialAngleRelaxation (Real.sqrt 2 - 1) C k d u v b < (41 / 50 : ℝ) := by
  apply (initialAngleRelaxation_le_diagonal hC0 (Real.sqrt 2 - 1) k d u v b).trans_lt
  rcases hhigh with hv0 | hu0
  · exact initialAngleRelaxation_diagonal_small_width hC0 hC1 hu1 hv0 hv1
  · rw [initialAngleRelaxation_diagonal_symm]
    exact initialAngleRelaxation_diagonal_small_width hC0 hC1 hv1 hu0 hu1

/-- The first region, the second region, the two bad apices, and the
strict complementary region cover the entire high-left parameter domain. -/
theorem initialAngleRelaxation_left_domain_lt {C k d s u v b : ℝ}
    (hKC : Real.sqrt 2 - 1 ≤ C) (hk0 : 3 / 8 ≤ k) (hk1 : k ≤ 4 / 5)
    (hs0 : 0 ≤ s) (hs2 : s ^ 2 = 1 + k ^ 2) (hkd : k * d = s - 1)
    (hbu : b ≤ u) (hu1 : u ≤ 2 * C) (hv0 : C ≤ v) (hv1 : v ≤ 2 * C)
    (hb1 : b ≤ 2 * C) (hcompat : u ≤ 2 * (1 - k) * C + k * b) :
    initialAngleRelaxation (Real.sqrt 2 - 1) C k d u v b < (5259 / 6400 : ℝ) := by
  obtain ⟨hK0, hK1⟩ := initialAngle_offset_bounds
  have hdpos := initialAngle_inset_pos (by linarith) hs0 hs2 hkd
  have hdK := initialAngle_inset_lt_offset (by linarith) (by linarith) hdpos
    (initialAngle_inset_equation (by linarith) hs2 hkd)
  have hstation := initialAngle_stationary_lt_rational (C := C) hk0 hk1 hs0 hs2 hkd
  rcases le_total (u + v) (2 * (Real.sqrt 2 - 1)) with hsum | hsum
  · linarith [initialAngleRelaxation_le_two_thirds_of_low_apex (by linarith) (by linarith)
      (by linarith) initialAngle_offset_sq hv0 hv1 hsum k d b]
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
  · exact (initialAngleRelaxation_complement_lt (by linarith) hk0 hk1 hs0 hs2 hkd hu1 hv1
      hcompat hu hY).trans (by norm_num)

/-- The finite-support estimate holds at every nonnegative width under
the ordinary support compatibility and either high-endpoint alternative. -/
theorem initialAngleRelaxation_all_width_lt {C k d s u v b : ℝ}
    (hC : 0 ≤ C) (hk0 : 3 / 8 ≤ k) (hk1 : k ≤ 4 / 5)
    (hs0 : 0 ≤ s) (hs2 : s ^ 2 = 1 + k ^ 2) (hkd : k * d = s - 1)
    (hbu : b ≤ u) (hu1 : u ≤ 2 * C) (hv1 : v ≤ 2 * C) (hb1 : b ≤ 2 * C)
    (hcompat : u ≤ 2 * (1 - k) * C + k * b) (hhigh : C ≤ v ∨ C ≤ b) :
    initialAngleRelaxation (Real.sqrt 2 - 1) C k d u v b < (5259 / 6400 : ℝ) := by
  rcases le_or_gt C (49 / 100) with hsmall | hsmall
  · exact (initialAngleRelaxation_small_width hC hsmall hu1 hv1
      (hhigh.imp_right fun hb => hb.trans hbu) k d b).trans (by norm_num)
  have hKC : Real.sqrt 2 - 1 ≤ C := by linarith [initialAngle_offset_bounds.2]
  rcases le_or_gt C v with hv0 | hv0
  · exact initialAngleRelaxation_left_domain_lt hKC hk0 hk1 hs0 hs2 hkd hbu hu1 hv0 hv1 hb1 hcompat
  have hdpos := initialAngle_inset_pos (by linarith) hs0 hs2 hkd
  have hdK := initialAngle_inset_lt_offset (by linarith) (by linarith) hdpos
    (initialAngle_inset_equation (by linarith) hs2 hkd)
  exact (initialAngleRelaxation_le_raise_left hC (by linarith) (by linarith)
    (by linarith [mul_nonneg (by linarith : 0 ≤ 1 - k) hdpos.le]) hu1 hv0.le
    (hhigh.resolve_left hv0.not_ge)).trans_lt (initialAngleRelaxation_left_domain_lt hKC hk0 hk1
      hs0 hs2 hkd hbu hu1 le_rfl (by linarith) hb1 hcompat)

end AmbidextrousSofa
