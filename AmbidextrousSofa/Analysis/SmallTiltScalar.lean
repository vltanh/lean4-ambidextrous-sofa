module

public import AmbidextrousSofa.Analysis.SmallTiltConstants

@[expose] public section

/-!
# Small positive tilts satisfy both initial-floor energy inequalities

The three wing chords and the ordinary-area comparison give a rational
lower bound for the ordinary area through the fixed tangent direction.
The shared radius-width cut makes a radius failure spend a joint height-and-niche
budget. The floor failure is paid by its linear width gain. Both use the same area prices. Every comparison is
on a full parameter interval. The geometric application supplies the chord
and area inequalities from the actual cap, its selected polygons, and its
actual outside niche integral.
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

  AmbidextrousSofa.Analysis.smallTiltHeightUpper
  AmbidextrousSofa.Analysis.smallTiltSineSquareUpper
  AmbidextrousSofa.Analysis.smallTiltSineUpper
  AmbidextrousSofa.Analysis.smallTiltSineFactor

namespace AmbidextrousSofa.Analysis

/-- Both initial-floor inequalities follow from the wing chords, the
ordinary-area comparison, actual niche bounds, and actual top overhang bounds. -/
theorem smallTilt_initialFloorEnergyConditions_of_area
    {C h z T J P V : ℝ}
    (hC0 : 2 / 3 ≤ C) (hC1 : C ≤ tiltedRadiusWidth)
    (hh0 : 0 < h) (hh1 : h ≤ tiltedBalanceHeight)
    (hz0 : 0 ≤ z)
    (hT : T ≤ initialFloorSine h) (hzT : z ≤ smallTiltProjection * T) (hJ : J ≤ tiltedLeakageMomentBound)
    (hchord : T + Real.sqrt ((C - T) ^ 2 + (1 / 2 - h / 4 - 3 * z / 4) ^ 2) +
      Real.sqrt (C ^ 2 + (1 / 2 - h / 4 + z / 4) ^ 2) ≤ 2 * P)
    (harea : P + C * (2 - h) - (T + J) * z / 2 ≤ V) (hV : V ≤ 2.2199) :
    InitialFloorEnergyConditions (3 * C) (tiltedEndpointMomentum h z 0) h := by
  norm_num [tiltedLeakageMomentBound, horizontalLeakageA0] at hJ
  norm_num [smallTiltProjection, smallTiltContainingWidth, squareRootNewton] at hzT
  have hhmax : h ≤ smallTiltHeightUpper := hh1.trans tiltedBalanceHeight_bounds.2
  have hcoarse : smallTiltHeightUpper < 1 / 12 := by norm_num
  have hsmax := smallTiltSineUpper_lt_third
  have hhhalf : h < 1 / 2 := hhmax.trans_lt (by norm_num)
  have hCbox : C ≤ smallTiltContainingWidth := by
    have hsq : 9 * C ^ 2 ≤ 5 := by
      nlinarith only [pow_le_pow_left₀ (by linarith only [hC0] : 0 ≤ C) hC1 2,
        tiltedRadiusWidth_sq, sq_nonneg tiltedRadiusMomentum]
    norm_num [smallTiltContainingWidth, squareRootNewton]
    nlinarith only [hsq, hC0]
  norm_num [smallTiltContainingWidth, squareRootNewton] at hCbox
  -- The 3–4–5 direction gives `P ≥ 4C/5 + 3/10 - 3(h+z)/20 + T/10`.
  -- Use the radius containing width, the overhang projection, and the integrated leakage moment for the two losses.
  have hlower : smallTiltBaseline + (2 + smallTiltTangent) * (C - smallTiltWidth) -
      smallTiltHeightLoss * h - smallTiltNicheLoss * z - T * z / 2 ≤ V := by
    have hright := smallTilt_tangent_le_norm (C - T) (1 / 2 - h / 4 - 3 * z / 4)
    have hleft := smallTilt_tangent_le_norm C (1 / 2 - h / 4 + z / 4)
    have hbase := smallTilt_baseline_rewrite C
    norm_num [smallTiltTangent, smallTiltVertical, smallTiltHeightLoss, smallTiltNicheLoss, smallTiltProjection, smallTiltContainingWidth, squareRootNewton]
      at hright hleft hbase ⊢
    linarith only [hright, hleft, hchord, harea, hzT, hbase,
      mul_le_mul_of_nonneg_right hCbox hh0.le, mul_le_mul_of_nonneg_right hJ hz0]
  obtain ⟨hs0, hs1, hhs⟩ := smallTilt_sine_bounds hh0 hhmax
  have hS2 := smallTilt_baseline_gt_ordinary_bound
  norm_num [smallTiltTangent, smallTiltHeightLoss, smallTiltNicheLoss, smallTiltVertical, smallTiltProjection, smallTiltContainingWidth, squareRootNewton] at hlower
  have hsq := initialFloorSine_sq hh0.le (by linarith only [hhhalf])
  have hTz := mul_le_mul_of_nonneg_right hT hz0
  set s := initialFloorSine h
  have hzs : z ≤ smallTiltProjection * s := by
    norm_num [smallTiltProjection, smallTiltContainingWidth, squareRootNewton]
    linarith only [hzT, hT]
  norm_num [smallTiltProjection, smallTiltContainingWidth, squareRootNewton] at hzs
  have hsum : h + z ≤ 1 / 2 := by
    linarith only [hhmax, hcoarse, hzs, hs1, hsmax]
  unfold tiltedEndpointMomentum
  constructor
  · -- The radius-width cut turns a failed radius test into one pressure budget.
    by_contra! hradius
    have hCrad : 9 * C ^ 2 ≤ 5 - tiltedRadiusMomentum ^ 2 := by
      nlinarith [pow_le_pow_left₀ (by linarith : 0 ≤ C) hC1 2, tiltedRadiusWidth_sq]
    have hBneg : -1 / 2 + 5 / 4 * h + 3 / 4 * z < 0 := by
      linarith only [hhmax, hzs, hs1, hsmax, hcoarse]
    have hbudget : h + 3 / 5 * z ≤ tiltedBalanceHeight := by
      have hb0 := tiltedRadiusMomentum_neg
      unfold tiltedRadiusMomentum tiltedBalanceMomentum at hCrad hb0
      nlinarith only [hradius, hCrad, hBneg, hb0]
    have hBsq : (-1 / 2 + 5 / 4 * h + 3 / 4 * z) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      nlinarith only [hh0, hz0, hBneg,
        mul_nonneg (show 0 ≤ 5 / 4 * h + 3 / 4 * z by positivity)
          (show 0 ≤ 1 - 5 / 4 * h - 3 / 4 * z by linarith)]
    have hwidth : Real.sqrt 19 / 6 < C :=
      lt_of_pow_lt_pow_left₀ 2 (by linarith only [hC0])
        (by nlinarith only [hradius, hBsq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 19)])
    have hpaid := smallTilt_radius_budget_payment hz0 (hT.trans hs1.le) hbudget
    have hgain := smallTilt_radius_gain_positive
    unfold smallTiltWidth at hlower
    norm_num [smallTiltHeightLoss, smallTiltNicheLoss, smallTiltTangent, smallTiltVertical, smallTiltProjection, smallTiltContainingWidth, squareRootNewton]
      at hpaid hgain
    linarith only [hlower, hV, hS2, hpaid, hgain,
      mul_lt_mul_of_pos_left hwidth (show (0 : ℝ) < 14 / 5 by norm_num)]
  · -- A floor test above `4` gives `3C - s/2 > √17/2 - (9/64)(h+z)²`: the square of the
    -- right side is at most `17/4 - (9/16)(h+z)²`. Then the area bound fails.
    by_contra! hQ
    have hδ : 0 ≤ Real.sqrt 17 - 4 - 9 / 64 * (h + z) ^ 2 := by
      have hroot := smallTilt_radical_bounds.1
      norm_num [squareRootNewton] at hroot
      nlinarith only [hroot, hh0, hz0, hsum]
    have hlt : (Real.sqrt 17 / 2 - 9 / 64 * (h + z) ^ 2) ^ 2 < (3 * C - s / 2) ^ 2 := by
      linarith only [hQ, hsq, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num),
        mul_nonneg (sq_nonneg (h + z)) hδ]
    have hwidth := lt_of_pow_lt_pow_left₀ 2 (by linarith only [hC0, hs1, hsmax]) hlt
    have hpositive := smallTilt_polynomial_positive hh0.le hs0 hs1.le hhs
    norm_num [smallTiltFloorLinear, smallTiltHeightLoss, smallTiltFloorQuadratic,
      smallTiltNicheLoss, smallTiltTangent, smallTiltVertical, smallTiltProjection, smallTiltContainingWidth, squareRootNewton] at hpositive
    unfold smallTiltWidth at hlower
    linarith only [hlower, hV, hS2, hTz, hzs,
      mul_lt_mul_of_pos_left hwidth (show (0 : ℝ) < 14 / 5 by norm_num),
      pow_le_pow_left₀ (add_nonneg hh0.le hz0) (add_le_add_right hzs h) 2,
      mul_le_mul_of_nonneg_left hzs hs0.le, hpositive]

end AmbidextrousSofa.Analysis
