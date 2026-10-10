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
    0 ≤ quadraticExcessLength ε := by
  have hs := Real.sq_sqrt (show 0 ≤ 1 + 4 * ε by linarith)
  have hs0 := Real.sqrt_nonneg (1 + 4 * ε)
  unfold quadraticExcessLength
  nlinarith

theorem quadraticExcessLength_identity {ε : ℝ} (hε : 0 ≤ ε) :
    ε = quadraticExcessLength ε / 2 + quadraticExcessLength ε ^ 2 / 4 := by
  have hs := Real.sq_sqrt (show 0 ≤ 1 + 4 * ε by linarith)
  unfold quadraticExcessLength
  nlinarith only [hs]

theorem quadraticExcessLength_lt {ε l : ℝ} (hε : 0 ≤ ε) (hl : 0 ≤ l)
    (hbound : ε < l / 2 + l ^ 2 / 4) : quadraticExcessLength ε < l := by
  have hid := quadraticExcessLength_identity hε
  have hnonneg := quadraticExcessLength_nonneg hε
  by_contra hnot
  have hprod := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hnot))
    (show 0 ≤ quadraticExcessLength ε + l + 2 by linarith)
  nlinarith only [hid, hprod, hbound]

/-- The strict endpoint-angle margin follows from a quadratic cosine
bound at the half-angle and the exact double-angle identity. -/
theorem cos_eleven_fifteenths_gt_thirty_seven_fiftieths :
    37 / 50 < Real.cos (11 / 15 : ℝ) := by
  have hhalf : (1679 / 1800 : ℝ) ≤ Real.cos (11 / 30 : ℝ) := by
    have h := Real.one_sub_sq_div_two_le_cos (x := (11 / 30 : ℝ))
    norm_num at h ⊢
    exact h
  have hprod := mul_nonneg (sub_nonneg.mpr hhalf)
    (show 0 ≤ Real.cos (11 / 30 : ℝ) + 1679 / 1800 by linarith)
  have hd := Real.cos_two_mul (11 / 30 : ℝ)
  rw [show 2 * (11 / 30 : ℝ) = 11 / 15 by norm_num] at hd
  nlinarith only [hprod, hd]

theorem eleven_fifteenths_lt_arccos_of_le {C : ℝ}
    (hC0 : -1 ≤ C) (hC1 : C ≤ 37 / 50) :
    11 / 15 < Real.arccos C := by
  have hc := Real.cos_arccos hC0 (by linarith only [hC1])
  by_contra hnot
  have hmono := Real.cos_le_cos_of_nonneg_of_le_pi
    (Real.arccos_nonneg C)
    (show (11 / 15 : ℝ) ≤ Real.pi by linarith only [Real.pi_gt_three])
    (le_of_not_gt hnot)
  rw [hc] at hmono
  linarith only [hmono, hC1, cos_eleven_fifteenths_gt_thirty_seven_fiftieths]

/-- A positive decreasing quadratic at the first crossing forces that
crossing to precede any point where the quadratic is already negative. -/
theorem first_zero_lt_of_quadratic {a A d e : ℝ}
    (had : a ≤ d) (hAd : A ≤ d)
    (hquad : 0 ≤ e - d * a + a ^ 2 / 2)
    (hnegative : e - d * A + A ^ 2 / 2 < 0) : a < A := by
  by_contra hnot
  have hprod := mul_nonpos_of_nonneg_of_nonpos
    (sub_nonneg.mpr (le_of_not_gt hnot))
    (show a + A - 2 * d ≤ 0 by linarith only [had, hAd])
  nlinarith only [hquad, hnegative, hprod]

/-- In the pre-floor case, the exact zero-source circle gives both a
short excess height and an early first zero. -/
theorem initial_circle_excess_bounds {d B a : ℝ}
    (hd0 : 2 ≤ d) (hd1 : d < 111 / 50)
    (hB0 : -7 / 12 < B) (hB1 : B < 7 / 40)
    (ha : a ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hp : initialFloorCircleP d B a = 0)
    (hq : 1 < initialFloorCircleQ d B a) :
    B < 0 ∧ a < 8 / 15 ∧ initialFloorCircleQ d B a - 1 < 7 / 100 ∧
      quadraticExcessLength (initialFloorCircleQ d B a - 1) < 2 / 15 := by
  have hradius := initialFloorCircle_radius d B a
  rw [hp] at hradius
  have hdsq : d ^ 2 < (111 / 50 : ℝ) ^ 2 := by
    nlinarith only [mul_pos (sub_pos.mpr hd1)
      (show 0 < 111 / 50 + d by linarith only [hd0])]
  have hBneg : B < 0 := by
    by_contra hnot
    have hBp : 0 ≤ B := le_of_not_gt hnot
    have hBsq : B ^ 2 < (7 / 40 : ℝ) ^ 2 := by
      nlinarith only [mul_pos (sub_pos.mpr hB1)
        (show 0 < 7 / 40 + B by linarith only [hBp])]
    nlinarith only [hradius, hdsq, hBsq, hq]
  have hs : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha.1
    (by linarith only [ha.2, Real.pi_pos])
  have hc : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ha.1, Real.pi_pos], ha.2⟩
  have hsin : Real.sin a ≤ 1 / 2 := by
    have hbcos := mul_nonpos_of_nonpos_of_nonneg hBneg.le hc.le
    have hdcos := mul_nonneg (sub_nonneg.mpr hd0) hs.le
    unfold initialFloorCircleP at hp
    nlinarith only [hp, hbcos, hdcos]
  have haearly : a < 8 / 15 := by
    by_contra hnot
    have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
      (show -(Real.pi / 2) ≤ (8 / 15 : ℝ) by linarith only [Real.pi_pos])
      ha.2.le (le_of_not_gt hnot)
    have hlow := Real.sin_gt_sub_cube (by norm_num : (0 : ℝ) < 8 / 15)
    norm_num at hlow
    linarith only [hmono, hlow, hsin]
  have hBsq : B ^ 2 < (7 / 12 : ℝ) ^ 2 := by
    have hprod := mul_pos (show 0 < B + 7 / 12 by linarith only [hB0])
      (show 0 < 7 / 12 - B by linarith only [hBneg])
    nlinarith only [hprod]
  have hqbound : initialFloorCircleQ d B a - 1 < 7 / 100 := by
    by_contra hnot
    have hqq : 207 / 100 ≤ initialFloorCircleQ d B a + 1 := by
      linarith only [le_of_not_gt hnot]
    have hprod := mul_nonneg (sub_nonneg.mpr hqq)
      (show 0 ≤ initialFloorCircleQ d B a + 1 + 207 / 100 by linarith only [hq])
    nlinarith only [hradius, hdsq, hBsq, hprod]
  exact ⟨hBneg, haearly, hqbound,
    quadraticExcessLength_lt (by linarith only [hq]) (by norm_num)
      (by nlinarith only [hqbound])⟩

/-- A rational chord suffices to exclude a positive first momentum
at the floor throughout the upper tilt interval. -/
theorem initial_floor_positive_forces_small_tilt {d B h : ℝ}
    (hd : 2 ≤ d) (hh0 : 0 ≤ h) (hh1 : h ≤ 17 / 50)
    (hB : B ≤ -1 / 4 + 5 / 4 * h)
    (hpositive : 0 < 1 + B * (1 - h) - d * initialFloorSine h) : h < 1 / 8 := by
  by_contra hnot
  have hlow : 1 / 8 ≤ h := le_of_not_gt hnot
  have hprod := mul_nonneg (sub_nonneg.mpr hlow) (sub_nonneg.mpr hh1)
  have hchord : (5 / 16 + 5 / 4 * h) ^ 2 ≤ h * (2 - h) := by
    nlinarith only [hprod, hlow]
  have hs0 := initialFloorSine_nonneg h
  have hsq := initialFloorSine_sq hh0 (by linarith only [hh1])
  have hs : 5 / 16 + 5 / 4 * h ≤ initialFloorSine h :=
    (sq_le_sq₀ (by linarith only [hh0]) hs0).mp (hchord.trans_eq hsq.symm)
  have hBmul := mul_le_mul_of_nonneg_right hB
    (show 0 ≤ 1 - h by linarith only [hh1])
  have hdroot := mul_nonneg (sub_nonneg.mpr hd) hs0
  nlinarith only [hBmul, hdroot, hs, hpositive, hlow, sq_nonneg h]

theorem initial_floor_test_medium_tilt_le {d B h : ℝ}
    (hd0 : 2 ≤ d) (hd1 : d ≤ 111 / 50)
    (hh0 : 1 / 25 ≤ h) (hh1 : h ≤ 1 / 8)
    (hB0 : -7 / 12 + 3 / 2 * h ≤ B)
    (hB1 : B ≤ -1 / 4 + 5 / 4 * h) :
    initialFloorTest d B h ≤ 10387 / 2500 := by
  have hdmono := initialFloorTest_mono_d (d := d) (D := (111 / 50 : ℝ)) (B := B) (h := h)
    (by linarith only [hh0])
    (by linarith only [hh1]) (by linarith only [hd0]) hd1
  have hBmono := initialFloorTest_mono_B (d := (111 / 50 : ℝ)) (h := h) hB1
    (by linarith only [hB0, hh0])
  have hupper : initialFloorTest (111 / 50) (-1 / 4 + 5 / 4 * h) h ≤ 10387 / 2500 := by
    apply initialFloorTest_affine_le_of_endpoint_bounds
      (l := (1 / 25 : ℝ)) (r := (1 / 8 : ℝ)) (sl := (7 / 25 : ℝ)) (sr := (15 / 32 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) ⟨hh0, hh1⟩ <;> norm_num
  exact hdmono.trans (hBmono.trans hupper)

theorem initial_floor_test_small_tilt_le {d B h : ℝ}
    (hd : 2 ≤ d) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 25)
    (hB0 : -7 / 12 ≤ B) (hB1 : B ≤ -1 / 5) :
    initialFloorTest d B h ≤ d ^ 2 - 4 / 25 := by
  have hs0 := initialFloorSine_nonneg h
  have hsq := initialFloorSine_sq hh0 (by linarith only [hh1])
  have hhprod := mul_nonneg hh0 (show 0 ≤ 1 - h by linarith only [hh1])
  have hhroot : h ≤ initialFloorSine h :=
    (sq_le_sq₀ hh0 hs0).mp (by nlinarith only [hsq, hhprod])
  have hBprod := mul_nonpos_of_nonpos_of_nonneg
    (show B + 1 / 5 ≤ 0 by linarith only [hB1])
    (show 0 ≤ B + 4 / 5 by linarith only [hB0])
  have hBh := mul_nonneg (show 0 ≤ B + 7 / 12 by linarith only [hB0]) hh0
  have hdroot := mul_nonneg (sub_nonneg.mpr hd) hs0
  unfold initialFloorTest
  nlinarith only [hBprod, hBh, hdroot, hhroot, hh0]

theorem medium_tilt_excess_stops_early {d ε a : ℝ}
    (hd : 2 ≤ d) (hε : 0 ≤ ε) (had : a ≤ d)
    (henergy : (2 + ε) ^ 2 ≤ 10387 / 2500)
    (hquad : 0 ≤ 29 / 32 - d * a + a ^ 2 / 2) :
    ε < 1 / 25 ∧ a < 3 / 5 ∧ quadraticExcessLength ε < 2 / 25 ∧
      a + quadraticExcessLength ε < 11 / 15 := by
  have he : ε < 1 / 25 := by nlinarith only [henergy, hε]
  have ha := first_zero_lt_of_quadratic had
    (show (3 / 5 : ℝ) ≤ d by linarith only [hd]) hquad
    (show 29 / 32 - d * (3 / 5) + (3 / 5) ^ 2 / 2 < 0 by linarith only [hd])
  have hl : quadraticExcessLength ε < 2 / 25 :=
    quadraticExcessLength_lt hε (by norm_num) (by nlinarith only [he])
  exact ⟨he, ha, hl, by linarith only [ha, hl]⟩

/-- Two rational width ranges replace the derivative argument for the
nested-root sum. Both give strict stopping time below `11/15`. -/
theorem small_tilt_excess_stops_early {d ε a : ℝ}
    (hd0 : 2 ≤ d) (hd1 : d ≤ 111 / 50) (hε : 0 ≤ ε) (had : a ≤ d)
    (henergy : (2 + ε) ^ 2 ≤ d ^ 2 - 4 / 25)
    (hquad : 0 ≤ 4 / 5 - d * a + a ^ 2 / 2) :
    ε < 19 / 100 ∧ quadraticExcessLength ε < 1 / 3 ∧
      a + quadraticExcessLength ε < 11 / 15 := by
  have hdSq : d ^ 2 ≤ (111 / 50 : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hd1)
      (show 0 ≤ 111 / 50 + d by linarith only [hd0])]
  have he : ε < 37 / 200 := by nlinarith only [henergy, hdSq, hε]
  have hl : quadraticExcessLength ε < 8 / 25 :=
    quadraticExcessLength_lt hε (by norm_num) (by nlinarith only [he])
  refine ⟨by linarith only [he], by linarith only [hl], ?_⟩
  by_cases hdcut : d ≤ 54 / 25
  · have hdsq : d ^ 2 ≤ (54 / 25 : ℝ) ^ 2 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hdcut)
        (show 0 ≤ 54 / 25 + d by linarith only [hd0])]
    have he' : ε < 13 / 100 := by nlinarith only [henergy, hdsq, hε]
    have hl' : quadraticExcessLength ε < 6 / 25 :=
      quadraticExcessLength_lt hε (by norm_num) (by nlinarith only [he'])
    have ha := first_zero_lt_of_quadratic had
      (show (23 / 50 : ℝ) ≤ d by linarith only [hd0]) hquad
      (show 4 / 5 - d * (23 / 50) + (23 / 50) ^ 2 / 2 < 0 by linarith only [hd0])
    linarith only [ha, hl']
  · have hdhigh : 54 / 25 ≤ d := (le_of_not_ge hdcut)
    have ha := first_zero_lt_of_quadratic had
      (show (41 / 100 : ℝ) ≤ d by linarith only [hdhigh]) hquad
      (show 4 / 5 - d * (41 / 100) + (41 / 100) ^ 2 / 2 < 0 by linarith only [hdhigh])
    linarith only [ha, hl]

end AmbidextrousSofa.Analysis
