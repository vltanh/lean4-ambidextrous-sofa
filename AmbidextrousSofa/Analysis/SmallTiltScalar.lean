module

public import AmbidextrousSofa.Analysis.SmallTiltConstants

@[expose] public section

/-!
# Small positive tilts satisfy both initial-floor energy inequalities

The two possible failures each contradict the displayed ordinary-area
lower bound. Every comparison is on a full parameter interval. The
geometric application supplies this lower bound from the actual cap,
its three wing chords, and its actual outside niche integral.
-/

noncomputable section

namespace AmbidextrousSofa.Analysis

/-- Both initial-floor inequalities follow from the ordinary-area
comparison, actual niche bounds, and actual top overhang bounds. -/
theorem smallTilt_initialFloorEnergyConditions_of_area
    {C h z T V : ℝ}
    (hC0 : 2 / 3 ≤ C) (hC1 : C ≤ 37 / 50)
    (hh0 : 0 < h) (hh1 : h ≤ 509 / 10000)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 33 / 100)
    (hT : T ≤ initialFloorSine h) (hzT : z ≤ (10 / 9) * T)
    (hV : V ≤ 22199 / 10000)
    (hlower : smallTiltBaseline + (2 + smallTiltTangent) * (C - smallTiltWidth) -
      (8871 / 10000) * h - (1839 / 25000) * z - T * z / 2 ≤ V) :
    InitialFloorEnergyConditions (3 * C) (tiltedEndpointMomentum h z 0) h := by
  obtain ⟨hs0, hs1, hhs⟩ := smallTilt_sine_bounds hh0 hh1
  obtain ⟨hS1, hW, hS2⟩ := smallTilt_baseline_bounds
  obtain ⟨ht1, ht2⟩ := smallTilt_tangent_bounds
  have hsq := initialFloorSine_sq hh0.le (by linarith only [hh1])
  have hTz := mul_le_mul_of_nonneg_right hT hz0
  set s := initialFloorSine h
  unfold tiltedEndpointMomentum
  constructor
  · -- A radius above `5` forces `C > 29/40` and `z < 27/100`, and then the area bound fails.
    by_contra! hradius
    have hC : 29 / 40 < C := by
      by_contra! hc
      nlinarith only [hradius, hc, hC0, hh0, hz0, hh1, hz1]
    have hx : 5 * h + 3 * z < 14 / 15 := by
      by_contra! hx
      nlinarith only [hradius, hx, hC0, hC1, hh1, hz1]
    have hz : z < 27 / 100 := by
      rcases le_or_gt h (1 / 40) with hh | hh
      · have := lt_of_pow_lt_pow_left₀ 2 (by norm_num)
          (show s ^ 2 < (9 / 40) ^ 2 by nlinarith only [hsq, hh, hh0])
        linarith only [this, hzT, hT]
      · linarith only [hx, hh]
    nlinarith only [hlower, hV, hS1, hW, ht1, hC, hz, hh1, hTz, hs1, hz0]
  · -- A floor test above `4` gives `3C - s/2 > √17/2 - (9/64)(h+z)²`: the square of the
    -- right side is at most `17/4 - (9/16)(h+z)²`. Then the area bound fails.
    by_contra! hQ
    have hzs : z ≤ 10 / 9 * s := by linarith only [hzT, hT]
    have hδ : 0 ≤ Real.sqrt 17 - 4 - 9 / 64 * (h + z) ^ 2 := by
      nlinarith only [smallTilt_radical_bounds.1, hh0, hz0, hh1, hz1]
    have hlt : (Real.sqrt 17 / 2 - 9 / 64 * (h + z) ^ 2) ^ 2 < (3 * C - s / 2) ^ 2 := by
      linarith only [hQ, hsq, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num),
        mul_nonneg (sq_nonneg (h + z)) hδ]
    have hwidth := lt_of_pow_lt_pow_left₀ 2 (by linarith only [hC0, hs1]) hlt
    unfold smallTiltWidth at hlower
    linarith only [hlower, hV, hS2, hTz, hzs,
      mul_lt_mul_of_pos_left hwidth (show 0 < 2 + smallTiltTangent by linarith only [ht1]),
      mul_nonneg (sub_nonneg.2 ht1.le) hs0.le, mul_nonneg (sub_nonneg.2 ht2.le) (sq_nonneg (h + z)),
      pow_le_pow_left₀ (add_nonneg hh0.le hz0) (add_le_add_right hzs h) 2,
      mul_le_mul_of_nonneg_left hzs hs0.le, smallTilt_polynomial_positive hh0.le hs0 hs1.le hhs]

end AmbidextrousSofa.Analysis
