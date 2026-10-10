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
  have hQ : initialAngleRightLoss C 0 u b = initialAngleRampLoss C u := by
    apply intervalIntegral.integral_congr
    intro x _
    rw [zero_mul, max_eq_left (le_max_left 0 (x - u)), max_comm]
  have hN : initialAngleNicheLoss K C 0 d u v b =
      ∫ x in (-C)..C, max 0 (min (u - K - x) (v - K + x)) := by
    apply intervalIntegral.integral_congr
    intro x _
    rw [zero_mul, max_eq_left (le_max_left 0 (min (u - K - x) (v - K + x)))]
  unfold initialAngleRelaxation
  rw [hQ, hN]

theorem initialAngleRelaxation_le_diagonal {C : ℝ} (hC : 0 ≤ C)
    (K k d u v b : ℝ) :
    initialAngleRelaxation K C k d u v b ≤ initialAngleRelaxation K C 0 0 u v 0 := by
  rw [initialAngleRelaxation_zero]
  have hQ := initialAngleRampLoss_le_rightLoss hC k u b
  have hN := initialAngle_diagonal_integral_le_nicheLoss hC K k d u v b
  unfold initialAngleRelaxation
  linarith only [hQ, hN]

/-- Only the diagonal relaxation is reflected here. -/
theorem initialAngleRelaxation_diagonal_symm (K C u v : ℝ) :
    initialAngleRelaxation K C 0 0 u v 0 = initialAngleRelaxation K C 0 0 v u 0 := by
  have hreflect : (∫ x in (-C)..C, max 0 (min (u - K - x) (v - K + x))) =
      ∫ x in (-C)..C, max 0 (min (v - K - x) (u - K + x)) := by
    calc
      _ = ∫ x in (-C)..C, max 0 (min (v - K - (-x)) (u - K + (-x))) := by
        apply intervalIntegral.integral_congr
        intro x _
        congr 1
        rw [sub_neg_eq_add, add_neg_eq_sub]
        exact min_comm _ _
      _ = _ := by
        simpa only [neg_neg] using intervalIntegral.integral_comp_neg
          (f := fun x : ℝ => max 0 (min (v - K - x) (u - K + x))) (a := -C) (b := C)
  rw [initialAngleRelaxation_zero, initialAngleRelaxation_zero, hreflect]
  ring

theorem initialAngleRelaxation_diagonal_eq {K C u v : ℝ}
    (hu0 : C ≤ u) (hu1 : u ≤ 2 * C) (hv0 : C ≤ v) (hv1 : v ≤ 2 * C) :
    initialAngleRelaxation K C 0 0 u v 0 = diagonalRelaxation (2 * C) 0 K u v := by
  have h := integral_tilted_diagonal_tent (a := 2 * C) (h := 0) (u := u) (v := v) K
    (by constructor <;> linarith)
  simp only [sub_zero, add_zero, show -(2 * C) / 2 = -C by ring,
    show (2 * C) / 2 = C by ring] at h
  have hfun : (fun x : ℝ => max 0 (min (u - K - x) (v - K + x))) =
      (fun x : ℝ => max (min (u - K - x) (v - K + x)) 0) :=
    funext (fun x => max_comm _ _)
  rw [initialAngleRelaxation_zero, initialAngleRampLoss_eq_square hu0 hu1,
    initialAngleRampLoss_eq_square hv0 hv1, hfun, h]
  unfold diagonalRelaxation
  simp only [sub_zero, mul_zero, zero_div, show (2 * C) / 2 = C by ring]
  ring

/-- The high-left diagonal relaxation is below `41/50` at every small
width, including supports below the exterior window and nonpositive apices. -/
theorem initialAngleRelaxation_diagonal_small_width {C u v : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 49 / 100)
    (hu1 : u ≤ 2 * C) (hv0 : C ≤ v) (hv1 : v ≤ 2 * C) :
    initialAngleRelaxation (Real.sqrt 2 - 1) C 0 0 u v 0 < (41 / 50 : ℝ) := by
  let K := Real.sqrt (2 : ℝ) - 1
  have hK0 : 0 ≤ K := by have h := initialAngle_offset_bounds.1; dsimp [K]; linarith
  have hK1 : K ≤ 5 / 12 := by have h := initialAngle_offset_bounds.2; dsimp [K]; linarith
  have hK : K ^ 2 + 2 * K = 1 := initialAngle_offset_sq
  change initialAngleRelaxation K C 0 0 u v 0 < (41 / 50 : ℝ)
  by_cases hK2 : K ≤ 2 * C
  · by_cases hu0 : C ≤ u
    · have hcritical := diagonalRelaxation_le_critical (2 * C) 0 K u v
        (by linarith) (by linarith) (by linarith)
      have hbound : initialAngleRelaxation K C 0 0 u v 0 ≤
          2 * C - 2 * (C - K / 2) ^ 2 := by
        rw [initialAngleRelaxation_diagonal_eq hu0 hu1 hv0 hv1]
        nlinarith only [hcritical]
      exact hbound.trans_lt (initialAngle_diagonal_small_width hC1)
    · by_cases hsum : u + v ≤ 2 * K
      · exact (initialAngleRelaxation_le_two_thirds_of_low_apex hC0 hK0 hK1 hK hv0 hv1
          hsum 0 0 0).trans_lt (by norm_num)
      · by_cases hapex : u - v ≤ -2 * C
        · exact (initialAngleRelaxation_le_two_thirds_of_left_apex hC0 hv0 hv1 hapex K 0 0 0).trans_lt
            (by norm_num)
        · have hp : (u - v) / 2 ∈ Icc (-C) C := by
            constructor <;> linarith [lt_of_not_ge hapex]
          have hfirst := initialAngleRelaxation_first_region_le (K := K) (C := C)
            (k := 0) (d := 0) (u := u) (v := v) (b := u) hK0 hK2
            (by norm_num) (by norm_num) le_rfl hv0 hv1
            (by linarith [lt_of_not_ge hsum]) hp (by linarith [lt_of_not_ge hu0])
          have hsame : initialAngleRelaxation K C 0 0 u v u =
              initialAngleRelaxation K C 0 0 u v 0 := by
            rw [initialAngleRelaxation_zero, initialAngleRelaxation_zero]
          rw [hsame] at hfirst
          have hbound : initialAngleRelaxation K C 0 0 u v 0 ≤
              2 * C - 2 * (C - K / 2) ^ 2 := by
            unfold initialAngleStationaryValue at hfirst
            nlinarith only [hfirst, sq_nonneg (u + v - 2 * C - K)]
          exact hbound.trans_lt (initialAngle_diagonal_small_width hC1)
  · have htrivial := initialAngleRelaxation_le_twice_width hC0 K 0 0 u v 0
    linarith [lt_of_not_ge hK2]

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
  let K := Real.sqrt (2 : ℝ) - 1
  have hK0 : 0 ≤ K := by have h := initialAngle_offset_bounds.1; dsimp [K]; linarith
  have hK1 : K ≤ 5 / 12 := by have h := initialAngle_offset_bounds.2; dsimp [K]; linarith
  have hK : K ^ 2 + 2 * K = 1 := initialAngle_offset_sq
  have hC : 0 ≤ C := hK0.trans hKC
  have hkpos : 0 < k := by linarith
  have hklt : k < 1 := by linarith
  have hdpos := initialAngle_inset_pos hkpos hs0 hs2 hkd
  have hdK := initialAngle_inset_lt_offset hkpos hklt hdpos
    (initialAngle_inset_equation hkpos hs2 hkd)
  have hstation := initialAngle_stationary_lt_rational (C := C) hk0 hk1 hs0 hs2 hkd
  change initialAngleRelaxation K C k d u v b < (5259 / 6400 : ℝ)
  by_cases hsum : u + v ≤ 2 * K
  · exact (initialAngleRelaxation_le_two_thirds_of_low_apex hC hK0 hK1 hK hv0 hv1 hsum
      k d b).trans_lt (by norm_num)
  · by_cases hapex : u - v ≤ -2 * C
    · exact (initialAngleRelaxation_le_two_thirds_of_left_apex hC hv0 hv1 hapex K k d b).trans_lt
        (by norm_num)
    · have hp : (u - v) / 2 ∈ Icc (-C) C := by
        constructor <;> linarith [lt_of_not_ge hapex]
      by_cases hu : u ≤ C + K
      · have hfirst := initialAngleRelaxation_first_region_le hK0 (by linarith : K ≤ 2 * C)
          hkpos.le hklt hbu hv0 hv1 (by linarith [lt_of_not_ge hsum]) hp hu
        have hbound : initialAngleRelaxation K C k d u v b ≤
            initialAngleStationaryValue K C k d := by
          nlinarith only [hfirst, sq_nonneg (u + v - 2 * C - K)]
        exact hbound.trans_lt hstation
      · by_cases hY : 0 ≤ (1 + k) * C + K - v + k * (b - d)
        · exact (initialAngleRelaxation_second_region_le hK0 hKC hkpos.le hklt hdpos.le
            (by linarith) hbu (by linarith [lt_of_not_ge hu]) hu1 hv0 hv1 hb1 hcompat hY).trans_lt
              hstation
        · exact (initialAngleRelaxation_complement_lt hC hk0 hk1 hs0 hs2 hkd hu1 hv1 hcompat
            (lt_of_not_ge hu) (lt_of_not_ge hY)).trans (by norm_num)

/-- AT's finite-support estimate holds at every nonnegative width under
the ordinary support compatibility and either high-endpoint alternative. -/
theorem initialAngleRelaxation_all_width_lt {C k d s u v b : ℝ}
    (hC : 0 ≤ C) (hk0 : 3 / 8 ≤ k) (hk1 : k ≤ 4 / 5)
    (hs0 : 0 ≤ s) (hs2 : s ^ 2 = 1 + k ^ 2) (hkd : k * d = s - 1)
    (hbu : b ≤ u) (hu1 : u ≤ 2 * C) (hv1 : v ≤ 2 * C) (hb1 : b ≤ 2 * C)
    (hcompat : u ≤ 2 * (1 - k) * C + k * b) (hhigh : C ≤ v ∨ C ≤ b) :
    initialAngleRelaxation (Real.sqrt 2 - 1) C k d u v b < (5259 / 6400 : ℝ) := by
  by_cases hsmall : C ≤ 49 / 100
  · have hhigh' : C ≤ v ∨ C ≤ u := hhigh.imp id (fun hb => hb.trans hbu)
    exact (initialAngleRelaxation_small_width hC hsmall hu1 hv1 hhigh' k d b).trans (by norm_num)
  · have hKC : Real.sqrt 2 - 1 ≤ C := by
      linarith [initialAngle_offset_bounds.2, lt_of_not_ge hsmall]
    by_cases hv0 : C ≤ v
    · exact initialAngleRelaxation_left_domain_lt hKC hk0 hk1 hs0 hs2 hkd hbu hu1 hv0 hv1 hb1 hcompat
    · have hb0 : C ≤ b := hhigh.resolve_left hv0
      have hkpos : 0 < k := by linarith
      have hklt : k < 1 := by linarith
      have hdpos := initialAngle_inset_pos hkpos hs0 hs2 hkd
      have hdK := initialAngle_inset_lt_offset hkpos hklt hdpos
        (initialAngle_inset_equation hkpos hs2 hkd)
      have hkdK : k * d ≤ Real.sqrt 2 - 1 := by
        nlinarith only [hdK, mul_nonneg (show 0 ≤ 1 - k by linarith) hdpos.le]
      have hraise := initialAngleRelaxation_le_raise_left hC (by linarith : 1 / 3 ≤ k)
        hklt hkdK hu1 (le_of_not_ge hv0) hb0
      exact hraise.trans_lt (initialAngleRelaxation_left_domain_lt hKC hk0 hk1 hs0 hs2 hkd
        hbu hu1 le_rfl (by linarith) hb1 hcompat)

end AmbidextrousSofa
