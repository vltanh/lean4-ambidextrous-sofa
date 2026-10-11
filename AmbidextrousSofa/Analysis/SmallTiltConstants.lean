module

public import AmbidextrousSofa.Analysis.TiltedInitialEnergyBounds

@[expose] public section

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
      5099 / 1000 < Real.sqrt (26 : ℝ) :=
  ⟨Real.lt_sqrt_of_sq_lt (by norm_num), (Real.sqrt_lt' (by norm_num)).2 (by norm_num),
    Real.lt_sqrt_of_sq_lt (by norm_num)⟩

theorem smallTilt_tangent_sq :
    26 * smallTiltTangent ^ 2 = 17 ∧
      smallTiltTangent ^ 2 + smallTiltVertical ^ 2 = 1 := by
  norm_num [smallTiltTangent, smallTiltVertical, div_pow, Real.sq_sqrt]

theorem smallTilt_tangent_bounds :
    8086 / 10000 < smallTiltTangent ∧ smallTiltTangent < 8087 / 10000 := by
  have hn : 0 ≤ smallTiltTangent := by unfold smallTiltTangent; positivity
  constructor <;> nlinarith [smallTilt_tangent_sq.1]

theorem smallTilt_vertical_and_overhang_bounds :
    0 ≤ smallTiltVertical / 4 ∧ smallTiltVertical / 4 < 1471 / 10000 ∧
      956 / 10000 < (1 - smallTiltTangent) / 2 := by
  refine ⟨by unfold smallTiltVertical; positivity, ?_, by linarith [smallTilt_tangent_bounds.2]⟩
  rw [smallTiltVertical, div_div, div_lt_iff₀ (by positivity)]
  linarith [smallTilt_radical_bounds.2.2]

theorem smallTilt_baseline_rewrite (C : ℝ) :
    smallTiltBaseline + (2 + smallTiltTangent) * (C - smallTiltWidth) =
      (2 + smallTiltTangent) * C + smallTiltVertical / 2 := by
  have : Real.sqrt (26 : ℝ) ≠ 0 := by positivity
  unfold smallTiltBaseline smallTiltTangent smallTiltWidth smallTiltVertical smallTiltRadius
  field_simp
  linear_combination 2 * Real.sq_sqrt (show (0 : ℝ) ≤ 26 by norm_num) -
    2 * Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)

theorem smallTilt_baseline_bounds :
    2669 / 1200 < smallTiltBaseline ∧ smallTiltWidth < 11 / 16 ∧
      22199 / 10000 < smallTiltBaseline := by
  obtain ⟨h1, h2, h3⟩ := smallTilt_radical_bounds
  unfold smallTiltBaseline smallTiltWidth smallTiltRadius
  exact ⟨by linarith, by linarith, by linarith⟩

theorem smallTilt_tangent_le_norm (x y : ℝ) :
    smallTiltTangent * x + smallTiltVertical * y ≤ Real.sqrt (x ^ 2 + y ^ 2) :=
  Real.le_sqrt_of_sq_le <| by
    linear_combination (x ^ 2 + y ^ 2) * smallTilt_tangent_sq.2 +
      sq_nonneg (smallTiltVertical * x - smallTiltTangent * y)

theorem smallTilt_sine_bounds {h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 509 / 10000) :
    0 < initialFloorSine h ∧ initialFloorSine h < 63 / 200 ∧
      h ≤ (10000 / 19491) * (initialFloorSine h) ^ 2 := by
  have hs0 := initialFloorSine_nonneg h
  have hs2 := initialFloorSine_sq hh0.le (by linarith)
  refine ⟨?_, by nlinarith, by nlinarith⟩
  nlinarith [mul_pos hh0 (show 0 < 2 - h by linarith)]

/-- A fixed rational comparison proves positivity on the whole small
height interval. There is no finite sampling or numerical optimization. -/
theorem smallTilt_polynomial_positive {h s : ℝ}
    (hh0 : 0 ≤ h) (hs0 : 0 < s) (hs1 : s ≤ 63 / 200)
    (hh : h ≤ (10000 / 19491) * s ^ 2) :
    0 < (11591 / 30000) * s - (8871 / 10000) * h - (5 / 9) * s ^ 2 -
      (84261 / 640000) * (h + (10 / 9) * s) ^ 2 := by
  have hsR : s ^ 2 ≤ 63 / 200 * s := by nlinarith
  have hlin : h + 10 / 9 * s ≤ (10 / 9 + 10000 / 19491 * (63 / 200)) * s := by linarith
  have := pow_le_pow_left₀ (by linarith) hlin 2
  linarith

end AmbidextrousSofa.Analysis
