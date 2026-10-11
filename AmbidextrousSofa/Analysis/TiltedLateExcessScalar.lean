module

public import AmbidextrousSofa.Analysis.TiltedInitialEnergyBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-!
# Exact late-excess estimates for the tilted first wing

These estimates use the actual first-zero and floor energies. The small
tilt case is split into two rational width intervals; the resulting
polynomial bounds avoid differentiating a nested square-root envelope.
No sampled numerical inequality is used.
-/

noncomputable section

open Set

namespace AmbidextrousSofa.Analysis

def quadraticExcessLength (ε : ℝ) : ℝ := Real.sqrt (1 + 4 * ε) - 1

theorem quadraticExcessLength_nonneg {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ quadraticExcessLength ε :=
  sub_nonneg.2 (Real.one_le_sqrt.2 (by linarith))

theorem quadraticExcessLength_identity {ε : ℝ} (hε : 0 ≤ ε) :
    ε = quadraticExcessLength ε / 2 + quadraticExcessLength ε ^ 2 / 4 := by
  unfold quadraticExcessLength
  linear_combination -Real.sq_sqrt (show 0 ≤ 1 + 4 * ε by linarith) / 4

theorem quadraticExcessLength_lt {ε l : ℝ} (hε : 0 ≤ ε) (hl : 0 ≤ l)
    (hbound : ε < l / 2 + l ^ 2 / 4) : quadraticExcessLength ε < l := by
  have := quadraticExcessLength_identity hε
  nlinarith [quadraticExcessLength_nonneg hε]

/-- The strict endpoint-angle margin follows from a quadratic cosine
bound at the half-angle and the exact double-angle identity. -/
theorem cos_eleven_fifteenths_gt_thirty_seven_fiftieths :
    37 / 50 < Real.cos (11 / 15 : ℝ) := by
  have h := Real.one_sub_sq_div_two_le_cos (x := (11 / 30 : ℝ))
  rw [show (11 / 15 : ℝ) = 2 * (11 / 30) by norm_num, Real.cos_two_mul]
  nlinarith

theorem eleven_fifteenths_lt_arccos_of_le {C : ℝ}
    (hC0 : -1 ≤ C) (hC1 : C ≤ 37 / 50) :
    11 / 15 < Real.arccos C := by
  rw [← Real.arccos_cos (x := 11 / 15) (by norm_num) (by linarith [Real.pi_gt_three])]
  exact Real.arccos_lt_arccos hC0
    (by linarith [cos_eleven_fifteenths_gt_thirty_seven_fiftieths]) (Real.cos_le_one _)

/-- A positive decreasing quadratic at the first crossing forces that
crossing to precede any point where the quadratic is already negative. -/
theorem first_zero_lt_of_quadratic {a A d e : ℝ}
    (had : a ≤ d) (hAd : A ≤ d)
    (hquad : 0 ≤ e - d * a + a ^ 2 / 2)
    (hnegative : e - d * A + A ^ 2 / 2 < 0) : a < A := by
  by_contra! h
  nlinarith [mul_nonneg (sub_nonneg.2 h) (by linarith : 0 ≤ 2 * d - a - A)]

/-- In the pre-floor case, the exact zero-source circle gives both a
short excess height and an early first zero. -/
theorem initial_circle_excess_bounds {d B a : ℝ}
    (hd0 : 2 ≤ d) (hd1 : d < 111 / 50)
    (hB0 : -7 / 12 < B) (hB1 : B < 7 / 40)
    (ha : a ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hp : initialFloorCircleP d B a = 0)
    (hq : 1 < initialFloorCircleQ d B a) :
    a < 8 / 15 ∧ initialFloorCircleQ d B a - 1 < 7 / 100 ∧
      quadraticExcessLength (initialFloorCircleQ d B a - 1) < 2 / 15 := by
  have hr := initialFloorCircle_radius d B a
  rw [hp] at hr
  have hB : B < 0 := by nlinarith
  have hq7 : initialFloorCircleQ d B a - 1 < 7 / 100 := by nlinarith
  refine ⟨?_, hq7, quadraticExcessLength_lt (by linarith) (by norm_num) (by linarith)⟩
  by_contra! h
  have := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) ha.2.le h
  have := Real.sin_gt_sub_cube (by norm_num : (0 : ℝ) < 8 / 15)
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [ha.1, Real.pi_pos], ha.2⟩
  unfold initialFloorCircleP at hp
  linarith [mul_neg_of_neg_of_pos hB hc, mul_nonneg (sub_nonneg.2 hd0)
    (Real.sin_nonneg_of_nonneg_of_le_pi ha.1.le (by linarith [ha.2, Real.pi_pos]))]

/-- A rational chord suffices to exclude a positive first momentum
at the floor throughout the upper tilt interval. -/
theorem initial_floor_positive_forces_small_tilt {d B h : ℝ}
    (hd : 2 ≤ d) (hh0 : 0 ≤ h) (hh1 : h ≤ 17 / 50)
    (hB : B ≤ -1 / 4 + 5 / 4 * h)
    (hpositive : 0 < 1 + B * (1 - h) - d * initialFloorSine h) : h < 1 / 8 := by
  by_contra! hlow
  have hs : 5 / 16 + 5 / 4 * h ≤ initialFloorSine h := Real.le_sqrt_of_sq_le (by nlinarith)
  nlinarith [mul_le_mul_of_nonneg_right hB (by linarith : 0 ≤ 1 - h),
    mul_nonneg (sub_nonneg.2 hd) (initialFloorSine_nonneg h)]

/-- In the medium tilt range a rational chord bounds the floor test, so the excess energy
stops the excess before `11/15`. -/
theorem medium_tilt_excess_stops_early {d B h ε a : ℝ}
    (hd0 : 2 ≤ d) (hd1 : d ≤ 111 / 50) (hh0 : 1 / 25 ≤ h) (hh1 : h ≤ 1 / 8)
    (hB0 : -7 / 12 + 3 / 2 * h ≤ B) (hB1 : B ≤ -1 / 4 + 5 / 4 * h) (hε : 0 ≤ ε) (had : a ≤ d)
    (henergy : (2 + ε) ^ 2 ≤ initialFloorTest d B h) (hquad : 0 ≤ 1 + B - d * a + a ^ 2 / 2) :
    ε < 19 / 100 ∧ quadraticExcessLength ε < 1 / 3 ∧ a + quadraticExcessLength ε < 11 / 15 := by
  have htest : initialFloorTest d B h ≤ 10387 / 2500 :=
    (initialFloorTest_mono_d (by linarith only [hh0]) (by linarith only [hh1])
      (by linarith only [hd0]) hd1).trans <|
      (initialFloorTest_mono_B hB1 (by linarith only [hB0, hh0, hh1])).trans <|
        initialFloorTest_affine_le_of_endpoint_bounds (l := 1 / 25) (r := 1 / 8) (sl := 7 / 25)
          (sr := 15 / 32) (by norm_num) (by norm_num) ⟨hh0, hh1⟩
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he : ε < 1 / 25 := by nlinarith only [henergy.trans htest, hε]
  have ha := first_zero_lt_of_quadratic had (by linarith only [hd0]) hquad
    (show 1 + B - d * (3 / 5) + (3 / 5) ^ 2 / 2 < 0 by linarith only [hB1, hh1, hd0])
  have hl := quadraticExcessLength_lt hε (by norm_num : (0 : ℝ) ≤ 2 / 25) (by linarith only [he])
  exact ⟨by linarith only [he], by linarith only [hl], by linarith only [ha, hl]⟩

/-- In the small tilt range two rational width ranges replace the derivative argument for the
nested-root sum. Both give strict stopping time below `11/15`. -/
theorem small_tilt_excess_stops_early {d B h ε a : ℝ}
    (hd0 : 2 ≤ d) (hd1 : d ≤ 111 / 50) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 25)
    (hB0 : -7 / 12 ≤ B) (hB1 : B ≤ -1 / 5) (hε : 0 ≤ ε) (had : a ≤ d)
    (henergy : (2 + ε) ^ 2 ≤ initialFloorTest d B h) (hquad : 0 ≤ 1 + B - d * a + a ^ 2 / 2) :
    ε < 19 / 100 ∧ quadraticExcessLength ε < 1 / 3 ∧ a + quadraticExcessLength ε < 11 / 15 := by
  have htest : initialFloorTest d B h ≤ d ^ 2 - 4 / 25 := by
    have hs0 := initialFloorSine_nonneg h
    have hhs : h ≤ initialFloorSine h := Real.le_sqrt_of_sq_le (by nlinarith only [hh0, hh1])
    unfold initialFloorTest
    nlinarith only [hB0, hB1, hhs, hh0, mul_nonneg (sub_nonneg.2 hd0) hs0,
      mul_nonneg (by linarith only [hB0] : 0 ≤ B + 7 / 12) hh0]
  replace henergy := henergy.trans htest
  have he : ε < 37 / 200 := by nlinarith only [henergy, hε, hd0, hd1]
  have hl := quadraticExcessLength_lt hε (by norm_num : (0 : ℝ) ≤ 8 / 25) (by linarith only [he])
  refine ⟨by linarith only [he], by linarith only [hl], ?_⟩
  rcases le_or_gt d (54 / 25) with hdcut | hdcut
  · have hl' := quadraticExcessLength_lt hε (by norm_num : (0 : ℝ) ≤ 6 / 25)
      (by nlinarith only [henergy, hε, hd0, hdcut])
    have ha := first_zero_lt_of_quadratic had (by linarith only [hd0]) hquad
      (show 1 + B - d * (23 / 50) + (23 / 50) ^ 2 / 2 < 0 by linarith only [hB1, hd0])
    linarith only [ha, hl']
  · have ha := first_zero_lt_of_quadratic had (by linarith only [hd0]) hquad
      (show 1 + B - d * (41 / 100) + (41 / 100) ^ 2 / 2 < 0 by linarith only [hB1, hdcut])
    linarith only [ha, hl]

end AmbidextrousSofa.Analysis
