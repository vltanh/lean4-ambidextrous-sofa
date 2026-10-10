import AmbidextrousSofa.Analysis.SmallTiltConstants

/-!
# Small positive tilts satisfy both initial-floor energy inequalities

The two possible failures each contradict the displayed ordinary-area
lower bound. Every comparison is on a full parameter interval. The
geometric application supplies this lower bound from the actual cap,
its three wing chords, and its actual outside niche integral.
-/

noncomputable section

namespace AmbidextrousSofa.Analysis

theorem smallTilt_initialFloorTest_square {C h z : ℝ}
    (hh0 : 0 ≤ h) (hh2 : h ≤ 2) :
    initialFloorTest (3 * C) (tiltedEndpointMomentum h z 0) h =
      (3 * C - initialFloorSine h / 2) ^ 2 + (9 / 16) * (h + z) ^ 2 - 1 / 4 := by
  have hs := initialFloorSine_sq hh0 hh2
  unfold initialFloorTest tiltedEndpointMomentum
  nlinarith only [hs]

/-- The square-root rationalization is expressed without a new radical:
the two positive quantities have sum greater than four, so their squared
difference bounds their difference with the exact factor `1/4`. -/
theorem smallTilt_width_growth_of_floorTest
    {C h z : ℝ} (hC : 2 / 3 ≤ C) (hh0 : 0 < h) (hh1 : h ≤ 509 / 10000)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 33 / 100)
    (hQ : 4 < initialFloorTest (3 * C) (tiltedEndpointMomentum h z 0) h) :
    initialFloorSine h / 6 - (3 / 64) * (h + z) ^ 2 < C - smallTiltWidth := by
  let X : ℝ := 3 * C - initialFloorSine h / 2
  let A : ℝ := Real.sqrt 17 / 2
  let w : ℝ := h + z
  have hs := smallTilt_sine_bounds hh0 hh1
  have hw0 : 0 ≤ w := by dsimp only [w]; linarith only [hh0, hz0]
  have hw1 : w < 2 / 3 := by dsimp only [w]; linarith only [hh1, hz1]
  have hwSq : w ^ 2 < 4 / 9 := by
    have hp := mul_pos (sub_pos.mpr hw1)
      (show 0 < 2 / 3 + w by linarith only [hw0])
    nlinarith only [hp]
  have hX0 : 0 < X := by dsimp only [X]; linarith only [hC, hs.2.1]
  have hA0 : 2 < A := by dsimp only [A]; linarith only [smallTilt_radical_bounds.1]
  have hASq : A ^ 2 = 17 / 4 := by
    dsimp only [A]
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)]
  rw [smallTilt_initialFloorTest_square hh0.le (by linarith only [hh1])] at hQ
  change 4 < X ^ 2 + (9 / 16) * w ^ 2 - 1 / 4 at hQ
  have hX2 : 2 < X := by
    by_contra hnot
    have hp := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hnot))
      (show 0 ≤ 2 + X by linarith only [hX0])
    nlinarith only [hp, hQ, hwSq]
  have hclaim : A - (9 / 64) * w ^ 2 < X := by
    by_contra hnot
    have hle := le_of_not_gt hnot
    have hXA : X ≤ A := hle.trans (sub_le_self _ (mul_nonneg (by norm_num) (sq_nonneg w)))
    have hp := mul_nonneg (sub_nonneg.mpr hXA)
      (show 0 ≤ A + X - 4 by linarith only [hA0, hX2])
    have hdiff : 4 * (A - X) ≤ A ^ 2 - X ^ 2 := by nlinarith only [hp]
    have hgap : A ^ 2 - X ^ 2 < (9 / 16) * w ^ 2 := by
      nlinarith only [hQ, hASq]
    linarith only [hle, hdiff, hgap]
  dsimp only [A, X, w] at hclaim
  unfold smallTiltWidth
  linarith only [hclaim]

theorem smallTilt_floorTest_le_four_of_area
    {C h z T V : ℝ}
    (hC : 2 / 3 ≤ C) (hh0 : 0 < h) (hh1 : h ≤ 509 / 10000)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 33 / 100)
    (hT : T ≤ initialFloorSine h) (hzT : z ≤ (10 / 9) * T)
    (hV : V ≤ 22199 / 10000)
    (hlower : smallTiltBaseline + (2 + smallTiltTangent) * (C - smallTiltWidth) -
      (8871 / 10000) * h - (1839 / 25000) * z - T * z / 2 ≤ V) :
    initialFloorTest (3 * C) (tiltedEndpointMomentum h z 0) h ≤ 4 := by
  by_contra hnot
  have hQ := lt_of_not_ge hnot
  let s := initialFloorSine h
  have hs := smallTilt_sine_bounds hh0 hh1
  have hs0 : 0 < s := hs.1
  have hs1 : s ≤ 63 / 200 := hs.2.1.le
  have hhs : h ≤ (10000 / 19491) * s ^ 2 := hs.2.2
  have hwidth := smallTilt_width_growth_of_floorTest hC hh0 hh1 hz0 hz1 hQ
  have hλ := smallTilt_tangent_bounds
  have hλ0 : 0 < 2 + smallTiltTangent := by linarith only [hλ.1]
  have hwidthmul := mul_lt_mul_of_pos_left hwidth hλ0
  have hslower := mul_nonneg
    (show 0 ≤ smallTiltTangent - 8086 / 10000 by linarith only [hλ.1]) hs0.le
  have hqupper := mul_nonneg
    (show 0 ≤ 8087 / 10000 - smallTiltTangent by linarith only [hλ.2])
    (sq_nonneg (h + z))
  have hzs : z ≤ (10 / 9) * s := hzT.trans
    (mul_le_mul_of_nonneg_left hT (by norm_num))
  have hsum : h + z ≤ h + (10 / 9) * s := by linarith only [hzs]
  have hsum0 : 0 ≤ (h + (10 / 9) * s) + (h + z) := by
    linarith only [hh0, hz0, hs0]
  have hsumSq : (h + z) ^ 2 ≤ (h + (10 / 9) * s) ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hsum) hsum0
    nlinarith only [hp]
  have hQloss := mul_le_mul_of_nonneg_left hsumSq
    (show (0 : ℝ) ≤ 84261 / 640000 by norm_num)
  have hEloss := mul_le_mul_of_nonneg_left hzs
    (show (0 : ℝ) ≤ 1839 / 25000 by norm_num)
  have hTloss : T * z / 2 ≤ (5 / 9) * s ^ 2 := by
    have hp := mul_le_mul_of_nonneg_right hT hz0
    have hq := mul_le_mul_of_nonneg_left hzs hs0.le
    nlinarith only [hp, hq]
  have harea : (11591 / 30000) * s - (8871 / 10000) * h - (5 / 9) * s ^ 2 -
      (84261 / 640000) * (h + (10 / 9) * s) ^ 2 < V - smallTiltBaseline := by
    change (2 + smallTiltTangent) * (s / 6 - (3 / 64) * (h + z) ^ 2) <
      (2 + smallTiltTangent) * (C - smallTiltWidth) at hwidthmul
    nlinarith only [hlower, hwidthmul, hslower, hqupper, hQloss, hEloss, hTloss]
  have hpositive := smallTilt_polynomial_positive hh0.le hs0 hs1 hhs
  linarith only [harea, hpositive, hV, smallTilt_baseline_bounds.2.2]

theorem smallTilt_radius_le_five_of_area
    {C h z T V : ℝ}
    (hC0 : 2 / 3 ≤ C) (hC1 : C ≤ 37 / 50)
    (hh0 : 0 < h) (hh1 : h ≤ 509 / 10000)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 33 / 100)
    (hT : T ≤ initialFloorSine h) (hzT : z ≤ (10 / 9) * T)
    (hV : V ≤ 22199 / 10000)
    (hlower : smallTiltBaseline + (2 + smallTiltTangent) * (C - smallTiltWidth) -
      (8871 / 10000) * h - (1839 / 25000) * z - T * z / 2 ≤ V) :
    (3 * C) ^ 2 + (tiltedEndpointMomentum h z 0) ^ 2 ≤ 5 := by
  by_contra hnot
  have hradius := lt_of_not_ge hnot
  let B := tiltedEndpointMomentum h z 0
  have hBlo : -1 / 2 < B := by
    dsimp only [B, tiltedEndpointMomentum]
    linarith only [hh0, hz0]
  have hBhi : B < 0 := by
    dsimp only [B, tiltedEndpointMomentum]
    linarith only [hh1, hz1]
  have hBsq : B ^ 2 < 1 / 4 := by
    have hp := mul_pos (show 0 < B + 1 / 2 by linarith only [hBlo])
      (show 0 < 1 / 2 - B by linarith only [hBhi])
    nlinarith only [hp]
  have hCbig : 29 / 40 < C := by
    by_contra hnotC
    have hp := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hnotC))
      (show 0 ≤ 29 / 40 + C by linarith only [hC0])
    change 5 < (3 * C) ^ 2 + B ^ 2 at hradius
    nlinarith only [hp, hradius, hBsq]
  have hCsq : C ^ 2 ≤ (37 / 50) ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hC1)
      (show 0 ≤ 37 / 50 + C by linarith only [hC0])
    nlinarith only [hp]
  have hBsquare : 16 / 225 < B ^ 2 := by
    change 5 < (3 * C) ^ 2 + B ^ 2 at hradius
    nlinarith only [hradius, hCsq]
  have hBbound : B < -4 / 15 := by
    by_contra hnotB
    have hp := mul_nonneg (show 0 ≤ B + 4 / 15 by linarith only [le_of_not_gt hnotB])
      (show 0 ≤ 4 / 15 - B by linarith only [hBhi])
    nlinarith only [hp, hBsquare]
  have hxi : (5 * h + 3 * z) / 4 < 7 / 30 := by
    dsimp only [B, tiltedEndpointMomentum] at hBbound
    linarith only [hBbound]
  let s := initialFloorSine h
  have hs := smallTilt_sine_bounds hh0 hh1
  have hzs : z ≤ (10 / 9) * s := hzT.trans
    (mul_le_mul_of_nonneg_left hT (by norm_num))
  have hzsharp : z < 27 / 100 := by
    by_cases hsmall : h ≤ 1 / 40
    · have hsquare := initialFloorSine_sq hh0.le (by linarith only [hh1])
      have hssmall : s < 9 / 40 := by
        by_contra hnots
        have hp := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hnots))
          (show 0 ≤ s + 9 / 40 by linarith only [hs.1])
        change s ^ 2 = h * (2 - h) at hsquare
        nlinarith only [hp, hsquare, hsmall, sq_nonneg h]
      linarith only [hzs, hssmall]
    · linarith only [hxi, lt_of_not_ge hsmall]
  have hwidth : 3 / 80 < C - smallTiltWidth := by
    linarith only [hCbig, smallTilt_baseline_bounds.2.1]
  have hλ : 14 / 5 < 2 + smallTiltTangent := by
    linarith only [smallTilt_tangent_bounds.1]
  have hprod1 := mul_lt_mul_of_pos_right hλ
    (show 0 < C - smallTiltWidth by linarith only [hwidth])
  have hprod2 := mul_lt_mul_of_pos_left hwidth (show (0 : ℝ) < 14 / 5 by norm_num)
  have hbase : 559 / 240 < smallTiltBaseline +
      (2 + smallTiltTangent) * (C - smallTiltWidth) := by
    linarith only [hprod1, hprod2, smallTilt_baseline_bounds.1]
  have hTbound : T ≤ 63 / 200 := hT.trans hs.2.1.le
  have hTloss : T * z / 2 ≤ (63 / 400) * z := by
    have hp := mul_le_mul_of_nonneg_right hTbound hz0
    linarith only [hp]
  have hzloss := mul_le_mul_of_nonneg_left hzsharp.le
    (show (0 : ℝ) ≤ 1839 / 25000 + 63 / 400 by norm_num)
  have hhloss := mul_le_mul_of_nonneg_left hh1
    (show (0 : ℝ) ≤ 8871 / 10000 by norm_num)
  have hfinal : 666488123 / 300000000 < V := by
    linarith only [hlower, hbase, hTloss, hzloss, hhloss]
  linarith only [hfinal, hV]

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
  exact ⟨smallTilt_radius_le_five_of_area hC0 hC1 hh0 hh1 hz0 hz1 hT hzT hV hlower,
    smallTilt_floorTest_le_four_of_area hC0 hh0 hh1 hz0 hz1 hT hzT hV hlower⟩

end AmbidextrousSofa.Analysis
