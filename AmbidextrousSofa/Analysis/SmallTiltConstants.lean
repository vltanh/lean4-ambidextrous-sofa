module

public import AmbidextrousSofa.Analysis.TiltedInitialEnergyBounds
public import AmbidextrousSofa.Analysis.HorizontalLeakageScalar

@[expose] public section

/-!
# A 3–4–5 supporting direction for small positive tilts

The unit direction `(4/5, 3/5)` gives a lower bound for both wing chords.
It avoids approximating an algebraic tangent direction. The width `sqrt 17 / 6`
comes from completing the square in the initial-floor energy test.
The final positivity estimate holds on the whole small-height interval.
-/

noncomputable section

attribute [local simp]
  AmbidextrousSofa.tiltedLeakageMomentBound
  AmbidextrousSofa.horizontalLeakageA0
  AmbidextrousSofa.Analysis.tiltedBalanceMomentum
  AmbidextrousSofa.Analysis.tiltedBalanceFloorOffset
  AmbidextrousSofa.Analysis.tiltedBalanceGap
  AmbidextrousSofa.Analysis.tiltedBalanceDerivative
  AmbidextrousSofa.Analysis.tiltedBalanceLowerStep
  AmbidextrousSofa.Analysis.tiltedBalanceUpperStep
  AmbidextrousSofa.Analysis.tiltedBalanceLower₁
  AmbidextrousSofa.Analysis.tiltedBalanceUpper₁
  AmbidextrousSofa.Analysis.tiltedBalanceLower₂
  AmbidextrousSofa.Analysis.tiltedBalanceUpper₂
  AmbidextrousSofa.Analysis.tiltedBalanceLower
  AmbidextrousSofa.Analysis.tiltedBalanceUpper

namespace AmbidextrousSofa.Analysis

@[local simp] def smallTiltHeightUpper : ℝ := tiltedBalanceUpper
@[local simp] def smallTiltSineSquareUpper : ℝ := smallTiltHeightUpper * (2 - smallTiltHeightUpper)
@[local simp] def smallTiltSineUpper : ℝ :=
  squareRootNewton smallTiltSineSquareUpper (1 / 3)
@[local simp] def smallTiltSineFactor : ℝ := 1 / (2 - smallTiltHeightUpper)

def smallTiltWidth : ℝ := Real.sqrt 17 / 6
def smallTiltTangent : ℝ := 4 / 5
def smallTiltVertical : ℝ := 3 / 5
def smallTiltBaseline : ℝ := (2 + smallTiltTangent) * smallTiltWidth + smallTiltVertical / 2

/-- Prices from the containing width, chord direction, leakage moment,
and top-overhang projection. Keep their geometric contributions visible. -/
@[local simp] def smallTiltProjection : ℝ := squareRootNewton 5 2 / 2

@[local simp] def smallTiltContainingWidth : ℝ := squareRootNewton 5 2 / 3

def smallTiltHeightLoss : ℝ := smallTiltContainingWidth + smallTiltVertical / 4
def smallTiltNicheLoss : ℝ :=
  smallTiltVertical / 4 + tiltedLeakageMomentBound / 2 - (1 - smallTiltTangent) / (2 * smallTiltProjection)
def smallTiltFloorLinear : ℝ := (2 + smallTiltTangent) / 6 - smallTiltProjection * smallTiltNicheLoss
def smallTiltFloorQuadratic : ℝ := (2 + smallTiltTangent) * (3 / 64)

theorem smallTilt_radical_bounds :
    (17 : ℝ) / squareRootNewton 17 4 < Real.sqrt 17 ∧
      Real.sqrt 17 < squareRootNewton 17 4 := by
  constructor
  · apply Real.lt_sqrt_of_sq_lt
    norm_num [squareRootNewton]
  · apply (Real.sqrt_lt' (by norm_num [squareRootNewton])).mpr
    norm_num [squareRootNewton]

theorem smallTilt_tangent_sq :
    smallTiltTangent ^ 2 + smallTiltVertical ^ 2 = 1 := by
  norm_num [smallTiltTangent, smallTiltVertical, smallTiltProjection, smallTiltContainingWidth, squareRootNewton]

theorem smallTilt_baseline_rewrite (C : ℝ) :
    smallTiltBaseline + (2 + smallTiltTangent) * (C - smallTiltWidth) =
      (2 + smallTiltTangent) * C + smallTiltVertical / 2 := by
  unfold smallTiltBaseline
  ring

theorem smallTilt_baseline_gt_ordinary_bound : 2.2199 < smallTiltBaseline := by
  have hroot : ((2.2199 : ℝ) - 3 / 10) * 15 / 7 < Real.sqrt 17 :=
    Real.lt_sqrt_of_sq_lt (by norm_num)
  unfold smallTiltBaseline smallTiltWidth smallTiltTangent smallTiltVertical
  linarith only [hroot]

theorem smallTilt_tangent_le_norm (x y : ℝ) :
    smallTiltTangent * x + smallTiltVertical * y ≤ Real.sqrt (x ^ 2 + y ^ 2) :=
  Real.le_sqrt_of_sq_le <| by
    linear_combination (x ^ 2 + y ^ 2) * smallTilt_tangent_sq +
      sq_nonneg (smallTiltVertical * x - smallTiltTangent * y)

theorem smallTiltSineUpper_lt_third : smallTiltSineUpper < 1 / 3 := by
  norm_num [squareRootNewton]

set_option maxHeartbeats 1000000 in
theorem smallTilt_sine_bounds {h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ smallTiltHeightUpper) :
    0 < initialFloorSine h ∧ initialFloorSine h < smallTiltSineUpper ∧
      h ≤ smallTiltSineFactor * (initialFloorSine h) ^ 2 := by
  have hu : smallTiltHeightUpper < 1 := by norm_num
  have hs0 := initialFloorSine_nonneg h
  have hs2 := initialFloorSine_sq hh0.le (by linarith only [hh1, hu])
  have hq : h * (2 - h) ≤ smallTiltSineSquareUpper := by
    change h * (2 - h) ≤ smallTiltHeightUpper * (2 - smallTiltHeightUpper)
    nlinarith only [mul_nonneg (sub_nonneg.mpr hh1)
      (by linarith only [hh1, hu] : 0 ≤ 2 - h - smallTiltHeightUpper)]
  have hr : smallTiltSineSquareUpper < smallTiltSineUpper ^ 2 := by norm_num [squareRootNewton]
  have hp : 0 < smallTiltSineUpper := by norm_num [squareRootNewton]
  have hf : 0 < smallTiltSineFactor := by norm_num
  refine ⟨?_, by nlinarith only [hs2, hq, hr, hp, hs0], ?_⟩
  · nlinarith only [hs2, hs0, mul_pos hh0 (show 0 < 2 - h by linarith only [hh1, hu])]
  · have hid : smallTiltSineFactor * (2 - smallTiltHeightUpper) = 1 := by norm_num
    have hmul := mul_nonneg hh0.le (sub_nonneg.mpr hh1)
    have hpaid := mul_le_mul_of_nonneg_left (show h * (2 - smallTiltHeightUpper) ≤
        (initialFloorSine h) ^ 2 by nlinarith only [hs2, hmul]) hf.le
    have hid_mul : smallTiltSineFactor * (h * (2 - smallTiltHeightUpper)) = h := by
      calc
        _ = h * (smallTiltSineFactor * (2 - smallTiltHeightUpper)) := by ring
        _ = h := by rw [hid, mul_one]
    rw [hid_mul] at hpaid
    exact hpaid

/-- The whole radius-failure budget is paid by the same ordinary-area
prices as the floor test. No additional niche cutoff is required. -/
theorem smallTilt_radius_budget_payment {h z T : ℝ}
    (hz : 0 ≤ z) (hT : T ≤ smallTiltSineUpper) (hbudget : h + 3 / 5 * z ≤ tiltedBalanceHeight) :
    smallTiltHeightLoss * h + smallTiltNicheLoss * z + T * z / 2 ≤
      smallTiltHeightLoss * tiltedBalanceHeight := by
  have hprice : smallTiltNicheLoss + smallTiltSineUpper / 2 ≤ 3 / 5 * smallTiltHeightLoss := by
    norm_num [smallTiltNicheLoss, smallTiltHeightLoss, smallTiltVertical, smallTiltTangent, smallTiltProjection, smallTiltContainingWidth, squareRootNewton]
  have hpaid := mul_le_mul_of_nonneg_left hbudget
    (show 0 ≤ smallTiltHeightLoss by norm_num [smallTiltHeightLoss, smallTiltVertical, smallTiltProjection, smallTiltContainingWidth, squareRootNewton])
  nlinarith only [hpaid, mul_le_mul_of_nonneg_right hprice hz, mul_le_mul_of_nonneg_right hT hz]

/-- The two circle radii differ by a fixed geometric gain. Rationalizing
their difference and using their common elementary bracket pays the height budget. -/
theorem smallTilt_radius_gain_positive :
    0 < (2 + smallTiltTangent) * (Real.sqrt 19 - Real.sqrt 17) / 6 -
      smallTiltHeightLoss * tiltedBalanceHeight := by
  have h19 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 19)
  have h17 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 17)
  have h19U : Real.sqrt (19 : ℝ) < 9 / 2 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have h17U : Real.sqrt (17 : ℝ) < 9 / 2 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hpos : 0 < Real.sqrt 19 - Real.sqrt 17 := by
    nlinarith [Real.sqrt_nonneg (19 : ℝ), Real.sqrt_nonneg (17 : ℝ)]
  have hdiff : (2 / 9 : ℝ) < Real.sqrt 19 - Real.sqrt 17 := by
    nlinarith [mul_pos hpos (show 0 < 9 - (Real.sqrt 19 + Real.sqrt 17) by linarith)]
  have hbound := tiltedBalanceHeight_bounds.2
  have hpaid := mul_le_mul_of_nonneg_left hbound
    (show 0 ≤ smallTiltHeightLoss by norm_num [smallTiltHeightLoss, smallTiltVertical, smallTiltProjection, smallTiltContainingWidth, squareRootNewton])
  norm_num [smallTiltTangent, smallTiltHeightLoss, smallTiltVertical, smallTiltProjection, smallTiltContainingWidth, squareRootNewton] at hpaid ⊢
  linarith only [hpaid, hdiff]

/-- If `h ≤ κs²` and `s ≤ r`, all three losses are quadratic in `s`.
Their common coefficient at `r` suffices to compare them with the linear gain. -/
theorem quadratic_losses_lt_linear {A D b Q κ ell h s r : ℝ}
    (hD : 0 ≤ D) (hb : 0 ≤ b) (hQ : 0 ≤ Q) (hκ : 0 ≤ κ) (hell : 0 ≤ ell)
    (hh0 : 0 ≤ h) (hs0 : 0 < s) (hs1 : s ≤ r) (hh : h ≤ κ * s ^ 2)
    (hmargin : (D * κ + b + Q * (ell + κ * r) ^ 2) * r < A) :
    0 < A * s - D * h - b * s ^ 2 - Q * (h + ell * s) ^ 2 := by
  have hs2 : s ^ 2 ≤ r * s := by nlinarith
  have hlin : h + ell * s ≤ (ell + κ * r) * s := by
    calc
      h + ell * s ≤ κ * s ^ 2 + ell * s := add_le_add_left hh _
      _ ≤ κ * (r * s) + ell * s := by gcongr
      _ = (ell + κ * r) * s := by ring
  have hloss : D * h + b * s ^ 2 + Q * (h + ell * s) ^ 2 ≤
      (D * κ + b + Q * (ell + κ * r) ^ 2) * s ^ 2 := by
    calc
      _ ≤ D * (κ * s ^ 2) + b * s ^ 2 + Q * ((ell + κ * r) * s) ^ 2 := by gcongr
      _ = _ := by ring
  have htotal := mul_le_mul_of_nonneg_left hs2
    (show 0 ≤ D * κ + b + Q * (ell + κ * r) ^ 2 by positivity)
  have hstrict := mul_lt_mul_of_pos_right hmargin hs0
  nlinarith only [hloss, htotal, hstrict]

/-- Apply the endpoint comparison to the small-tilt losses. The sine bound
is obtained by one Newton step from the canonical height bound at the balance bracket. -/
theorem smallTilt_polynomial_positive {h s : ℝ}
    (hh0 : 0 ≤ h) (hs0 : 0 < s) (hs1 : s ≤ smallTiltSineUpper)
    (hh : h ≤ smallTiltSineFactor * s ^ 2) :
    0 < smallTiltFloorLinear * s - smallTiltHeightLoss * h - (smallTiltProjection / 2) * s ^ 2 -
      smallTiltFloorQuadratic * (h + smallTiltProjection * s) ^ 2 := by
  apply quadratic_losses_lt_linear
    (by norm_num [smallTiltHeightLoss, smallTiltVertical, smallTiltProjection, smallTiltContainingWidth, squareRootNewton]) (by norm_num)
    (by norm_num [smallTiltFloorQuadratic, smallTiltTangent])
    (by norm_num) (by norm_num) hh0 hs0 hs1 hh
  all_goals norm_num [smallTiltFloorLinear, smallTiltHeightLoss, smallTiltFloorQuadratic,
    smallTiltNicheLoss, smallTiltTangent, smallTiltVertical, smallTiltProjection, smallTiltContainingWidth, squareRootNewton]

end AmbidextrousSofa.Analysis
