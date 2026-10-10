import AmbidextrousSofa.Analysis.TiltedInitialEnergyBounds

/-!
# The fixed tangent and rational margins for small positive tilts

All constants are explicit radicals or rationals. The norm estimate is
the squared Cauchy identity at the fixed direction `(sqrt 17, 3)`.
The final positivity margin is a rational identity on a whole interval.
-/

noncomputable section

namespace AmbidextrousSofa.Analysis

def smallTiltWidth : ℝ := Real.sqrt 17 / 6
def smallTiltRadius : ℝ := Real.sqrt 26 / 6
def smallTiltBaseline : ℝ := 2 * smallTiltWidth + smallTiltRadius
def smallTiltTangent : ℝ := Real.sqrt 17 / Real.sqrt 26
def smallTiltVertical : ℝ := 3 / Real.sqrt 26

theorem smallTilt_radical_bounds :
    4123 / 1000 < Real.sqrt (17 : ℝ) ∧ Real.sqrt (17 : ℝ) < 33 / 8 ∧
      5099 / 1000 < Real.sqrt (26 : ℝ) := by
  have h17 := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
  have h26 := Real.sq_sqrt (show (0 : ℝ) ≤ 26 by norm_num)
  have h17n := Real.sqrt_nonneg (17 : ℝ)
  have h26n := Real.sqrt_nonneg (26 : ℝ)
  refine ⟨?_, ?_, ?_⟩
  · by_contra hnot
    have hle := le_of_not_gt hnot
    have hp := mul_nonneg (sub_nonneg.mpr hle)
      (show 0 ≤ 4123 / 1000 + Real.sqrt (17 : ℝ) by linarith only [h17n])
    nlinarith only [hp, h17]
  · by_contra hnot
    have hle := le_of_not_gt hnot
    have hp := mul_nonneg (sub_nonneg.mpr hle)
      (show 0 ≤ Real.sqrt (17 : ℝ) + 33 / 8 by linarith only [h17n])
    nlinarith only [hp, h17]
  · by_contra hnot
    have hle := le_of_not_gt hnot
    have hp := mul_nonneg (sub_nonneg.mpr hle)
      (show 0 ≤ 5099 / 1000 + Real.sqrt (26 : ℝ) by linarith only [h26n])
    nlinarith only [hp, h26]

theorem smallTilt_tangent_sq :
    26 * smallTiltTangent ^ 2 = 17 ∧
      smallTiltTangent ^ 2 + smallTiltVertical ^ 2 = 1 := by
  norm_num [smallTiltTangent, smallTiltVertical, div_pow, Real.sq_sqrt]

theorem smallTilt_tangent_bounds :
    8086 / 10000 < smallTiltTangent ∧ smallTiltTangent < 8087 / 10000 := by
  have hn : 0 ≤ smallTiltTangent := by unfold smallTiltTangent; positivity
  have heq := smallTilt_tangent_sq.1
  constructor
  · by_contra hnot
    have hle := le_of_not_gt hnot
    have hp := mul_nonneg (sub_nonneg.mpr hle)
      (show 0 ≤ 8086 / 10000 + smallTiltTangent by linarith only [hn])
    nlinarith only [hp, heq]
  · by_contra hnot
    have hle := le_of_not_gt hnot
    have hp := mul_nonneg (sub_nonneg.mpr hle)
      (show 0 ≤ smallTiltTangent + 8087 / 10000 by linarith only [hn])
    nlinarith only [hp, heq]

theorem smallTilt_vertical_and_overhang_bounds :
    0 ≤ smallTiltVertical / 4 ∧ smallTiltVertical / 4 < 1471 / 10000 ∧
      956 / 10000 < (1 - smallTiltTangent) / 2 := by
  have hd : 0 < Real.sqrt (26 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨by unfold smallTiltVertical; positivity, ?_, ?_⟩
  · change (3 / Real.sqrt (26 : ℝ)) / 4 < 1471 / 10000
    rw [div_div]
    apply (div_lt_iff₀ (mul_pos hd (by norm_num))).mpr
    linarith only [smallTilt_radical_bounds.2.2]
  · linarith only [smallTilt_tangent_bounds.2]

theorem smallTilt_calibration :
    smallTiltTangent * smallTiltWidth + smallTiltVertical / 2 = smallTiltRadius := by
  have hd : Real.sqrt (26 : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (show (0 : ℝ) < 26 by norm_num)).ne'
  unfold smallTiltTangent smallTiltWidth smallTiltVertical smallTiltRadius
  field_simp [hd]
  nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num),
    Real.sq_sqrt (show (0 : ℝ) ≤ 26 by norm_num)]

theorem smallTilt_baseline_rewrite (C : ℝ) :
    smallTiltBaseline + (2 + smallTiltTangent) * (C - smallTiltWidth) =
      (2 + smallTiltTangent) * C + smallTiltVertical / 2 := by
  unfold smallTiltBaseline
  nlinarith only [smallTilt_calibration]

theorem smallTilt_baseline_bounds :
    2669 / 1200 < smallTiltBaseline ∧ smallTiltWidth < 11 / 16 ∧
      22199 / 10000 < smallTiltBaseline := by
  have hr := smallTilt_radical_bounds
  have hS : 2669 / 1200 < smallTiltBaseline := by
    unfold smallTiltBaseline smallTiltWidth smallTiltRadius
    linarith only [hr.1, hr.2.2]
  exact ⟨hS, by unfold smallTiltWidth; linarith only [hr.2.1], by linarith only [hS]⟩

theorem smallTilt_tangent_le_norm (x y : ℝ) :
    smallTiltTangent * x + smallTiltVertical * y ≤ Real.sqrt (x ^ 2 + y ^ 2) := by
  have hid : (smallTiltTangent * x + smallTiltVertical * y) ^ 2 +
      (smallTiltVertical * x - smallTiltTangent * y) ^ 2 = x ^ 2 + y ^ 2 := by
    calc
      _ = (smallTiltTangent ^ 2 + smallTiltVertical ^ 2) * (x ^ 2 + y ^ 2) := by ring
      _ = x ^ 2 + y ^ 2 := by rw [smallTilt_tangent_sq.2, one_mul]
  have hs := Real.sq_sqrt (add_nonneg (sq_nonneg x) (sq_nonneg y))
  have hn := Real.sqrt_nonneg (x ^ 2 + y ^ 2)
  by_contra hnot
  have hgt := lt_of_not_ge hnot
  have hp := mul_pos (sub_pos.mpr hgt)
    (show 0 < smallTiltTangent * x + smallTiltVertical * y +
      Real.sqrt (x ^ 2 + y ^ 2) by linarith only [hgt, hn])
  nlinarith only [hp, hid, hs, sq_nonneg (smallTiltVertical * x - smallTiltTangent * y)]

theorem smallTilt_sine_bounds {h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 509 / 10000) :
    0 < initialFloorSine h ∧ initialFloorSine h < 63 / 200 ∧
      h ≤ (10000 / 19491) * (initialFloorSine h) ^ 2 := by
  have hs0 := initialFloorSine_nonneg h
  have hs2 := initialFloorSine_sq hh0.le (by linarith only [hh1])
  have hrad : 0 < h * (2 - h) := mul_pos hh0 (by linarith only [hh1])
  have hpos : 0 < initialFloorSine h := by nlinarith only [hs0, hs2, hrad]
  have hupper : (initialFloorSine h) ^ 2 ≤
      (509 / 10000) * (19491 / 10000) := by
    have hp := mul_nonneg (sub_nonneg.mpr hh1)
      (show 0 ≤ 2 - 509 / 10000 - h by linarith only [hh1])
    nlinarith only [hp, hs2]
  have hlt : initialFloorSine h < 63 / 200 := by
    by_contra hnot
    have hp := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hnot))
      (show 0 ≤ initialFloorSine h + 63 / 200 by linarith only [hs0])
    nlinarith only [hp, hupper]
  have hp := mul_nonneg hh0.le (sub_nonneg.mpr hh1)
  exact ⟨hpos, hlt, by nlinarith only [hs2, hp]⟩

/-- A fixed rational comparison proves positivity on the whole small
height interval. There is no finite sampling or numerical optimization. -/
theorem smallTilt_polynomial_positive {h s : ℝ}
    (hh0 : 0 ≤ h) (hs0 : 0 < s) (hs1 : s ≤ 63 / 200)
    (hh : h ≤ (10000 / 19491) * s ^ 2) :
    0 < (11591 / 30000) * s - (8871 / 10000) * h - (5 / 9) * s ^ 2 -
      (84261 / 640000) * (h + (10 / 9) * s) ^ 2 := by
  let k : ℝ := 10000 / 19491
  let R : ℝ := 63 / 200
  let c : ℝ := 10 / 9 + k * R
  let D : ℝ := 8871 / 10000
  let Q : ℝ := 84261 / 640000
  let F : ℝ := D * k + 5 / 9 + Q * c ^ 2
  have hk : 0 ≤ k := by norm_num [k]
  have hc : 0 ≤ c := by norm_num [c, k, R]
  have hD : 0 ≤ D := by norm_num [D]
  have hQ : 0 ≤ Q := by norm_num [Q]
  have hF : 0 ≤ F := by norm_num [F, D, k, Q, c, R]
  have hsR : s ^ 2 ≤ R * s := by
    have hp := mul_nonneg hs0.le (sub_nonneg.mpr hs1)
    dsimp only [R]
    nlinarith only [hp]
  have hh' : h ≤ k * s ^ 2 := hh
  have hlin : h + (10 / 9) * s ≤ c * s := by
    have hp := mul_le_mul_of_nonneg_left hsR hk
    dsimp only [c]
    nlinarith only [hh', hp]
  have hsum : 0 ≤ c * s + (h + (10 / 9) * s) := by
    nlinarith only [mul_nonneg hc hs0.le, hh0, hs0]
  have hsumSq : (h + (10 / 9) * s) ^ 2 ≤ c ^ 2 * s ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hlin) hsum
    nlinarith only [hp]
  have hDh := mul_le_mul_of_nonneg_left hh' hD
  have hQh := mul_le_mul_of_nonneg_left hsumSq hQ
  have hFs := mul_le_mul_of_nonneg_left hsR hF
  have hmargin : (11591 / 30000) - F * R = 11102231813 / 13507522880000 := by
    norm_num [F, D, k, Q, c, R]
  have hpositive : 0 < ((11591 / 30000) - F * R) * s :=
    mul_pos (by rw [hmargin]; norm_num) hs0
  change 0 < (11591 / 30000) * s - D * h - (5 / 9) * s ^ 2 -
    Q * (h + (10 / 9) * s) ^ 2
  dsimp only [F] at hFs hpositive
  nlinarith only [hDh, hQh, hFs, hpositive]

end AmbidextrousSofa.Analysis
