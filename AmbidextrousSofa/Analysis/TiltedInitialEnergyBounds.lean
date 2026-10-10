module

public import AmbidextrousSofa.Analysis.TiltedInitialEnergy

@[expose] public section

/-!
# Exact parameter strips for the initial-floor energy test

The square-root estimates below hold on entire intervals. They follow
from the concavity identity for the upper unit semicircle, proved by
squaring a convex combination. The endpoint pressure and box inputs are
ordinary geometric scalar bounds, and the conclusions are the two
explicit initial-floor energy inequalities.
-/

noncomputable section

open Set

namespace AmbidextrousSofa.Analysis

def initialFloorTest (d B h : ℝ) : ℝ :=
  d ^ 2 + B ^ 2 + B * (1 - h) - d * initialFloorSine h

def tiltedBoxHeight (C : ℝ) : ℝ := 1 - Real.sqrt (1 - C ^ 2)

def tiltedEndpointMomentum (h z w : ℝ) : ℝ :=
  -1 / 2 + 5 / 4 * h + 3 / 4 * z - w / 4

/-- A rational chord below the upper semicircle stays below it. -/
theorem initialFloorSine_convex_comb_lower
    {x y sx sy w : ℝ}
    (hx0 : 0 ≤ x) (hx2 : x ≤ 2) (hy0 : 0 ≤ y) (hy2 : y ≤ 2)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hsx : sx ^ 2 ≤ x * (2 - x)) (hsy : sy ^ 2 ≤ y * (2 - y)) :
    (1 - w) * sx + w * sy ≤ initialFloorSine ((1 - w) * x + w * y) := by
  have hw : 0 ≤ 1 - w := sub_nonneg.mpr hw1
  have hz0 : 0 ≤ (1 - w) * x + w * y :=
    add_nonneg (mul_nonneg hw hx0) (mul_nonneg hw0 hy0)
  have hz2 : (1 - w) * x + w * y ≤ 2 := by
    nlinarith [mul_nonneg hw (sub_nonneg.mpr hx2),
      mul_nonneg hw0 (sub_nonneg.mpr hy2)]
  have hsq := initialFloorSine_sq hz0 hz2
  have hnonneg := initialFloorSine_nonneg ((1 - w) * x + w * y)
  have hfirst := mul_nonneg hw (sub_nonneg.mpr hsx)
  have hsecond := mul_nonneg hw0 (sub_nonneg.mpr hsy)
  have hthird := mul_nonneg (mul_nonneg hw0 hw)
    (add_nonneg (sq_nonneg (x - y)) (sq_nonneg (sx - sy)))
  have hchord : ((1 - w) * sx + w * sy) ^ 2 ≤
      ((1 - w) * x + w * y) * (2 - ((1 - w) * x + w * y)) := by
    nlinarith
  by_contra hnle
  have hgt := lt_of_not_ge hnle
  have hprod := mul_pos (sub_pos.mpr hgt)
    (show 0 < (1 - w) * sx + w * sy +
      initialFloorSine ((1 - w) * x + w * y) by linarith)
  nlinarith

/-- The polynomial part has quadratic coefficient `5/16`; the
semicircle chord gives the remaining convexity estimate directly. -/
theorem initialFloorTest_affine_le_of_endpoint_bounds
    {d A l r sl sr h K : ℝ}
    (hd : 0 ≤ d) (hlr : l < r) (hl : 0 ≤ l) (hr : r ≤ 2)
    (hh : h ∈ Icc l r)
    (hsl : sl ^ 2 ≤ l * (2 - l)) (hsr : sr ^ 2 ≤ r * (2 - r))
    (hleft : d ^ 2 + (A + 5 / 4 * l) ^ 2 +
      (A + 5 / 4 * l) * (1 - l) - d * sl ≤ K)
    (hright : d ^ 2 + (A + 5 / 4 * r) ^ 2 +
      (A + 5 / 4 * r) * (1 - r) - d * sr ≤ K) :
    initialFloorTest d (A + 5 / 4 * h) h ≤ K := by
  let w : ℝ := (h - l) / (r - l)
  have hrl : 0 < r - l := sub_pos.mpr hlr
  have hw0 : 0 ≤ w := div_nonneg (sub_nonneg.mpr hh.1) hrl.le
  have hw1 : w ≤ 1 := by
    dsimp [w]
    apply (div_le_iff₀ hrl).2
    linarith [hh.2]
  have hblend : (1 - w) * l + w * r = h := by
    dsimp [w]
    field_simp [ne_of_gt hrl]
    ring
  have hroot : (1 - w) * sl + w * sr ≤ initialFloorSine h := by
    simpa only [hblend] using initialFloorSine_convex_comb_lower
      hl (by linarith) (by linarith) hr hw0 hw1 hsl hsr
  let Ql := d ^ 2 + (A + 5 / 4 * l) ^ 2 +
    (A + 5 / 4 * l) * (1 - l) - d * sl
  let Qr := d ^ 2 + (A + 5 / 4 * r) ^ 2 +
    (A + 5 / 4 * r) * (1 - r) - d * sr
  have hpoly : d ^ 2 + (A + 5 / 4 * h) ^ 2 +
      (A + 5 / 4 * h) * (1 - h) - d * ((1 - w) * sl + w * sr) =
        (1 - w) * Ql + w * Qr - 5 / 16 * (r - l) ^ 2 * w * (1 - w) := by
    rw [← hblend]
    dsimp [Ql, Qr]
    ring
  have herr : 0 ≤ 5 / 16 * (r - l) ^ 2 * w * (1 - w) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hw0)
      (sub_nonneg.mpr hw1)
  have hweighted : (1 - w) * Ql + w * Qr ≤ K := by
    calc
      _ ≤ (1 - w) * K + w * K := add_le_add
        (mul_le_mul_of_nonneg_left hleft (sub_nonneg.mpr hw1))
        (mul_le_mul_of_nonneg_left hright hw0)
      _ = K := by ring
  calc
    initialFloorTest d (A + 5 / 4 * h) h ≤
        d ^ 2 + (A + 5 / 4 * h) ^ 2 + (A + 5 / 4 * h) * (1 - h) -
          d * ((1 - w) * sl + w * sr) := by
      unfold initialFloorTest
      linarith [mul_le_mul_of_nonneg_left hroot hd]
    _ = (1 - w) * Ql + w * Qr - 5 / 16 * (r - l) ^ 2 * w * (1 - w) := hpoly
    _ ≤ (1 - w) * Ql + w * Qr := sub_le_self _ herr
    _ ≤ K := hweighted

theorem initialFloorTest_mono_d {d D B h : ℝ}
    (h0 : 0 ≤ h) (h2 : h ≤ 2) (hd : 1 / 2 ≤ d) (hdD : d ≤ D) :
    initialFloorTest d B h ≤ initialFloorTest D B h := by
  have hs := initialFloorSine_le_one h0 h2
  have hprod := mul_nonneg (sub_nonneg.mpr hdD)
    (show 0 ≤ D + d - initialFloorSine h by linarith)
  unfold initialFloorTest
  nlinarith

theorem initialFloorTest_mono_B {d B U h : ℝ}
    (hBU : B ≤ U) (hsum : 0 ≤ B + U + 1 - h) :
    initialFloorTest d B h ≤ initialFloorTest d U h := by
  have hprod := mul_nonneg (sub_nonneg.mpr hBU) hsum
  unfold initialFloorTest
  nlinarith

theorem tiltedBoxHeight_lt_of_width_bound {C D H : ℝ}
    (hC0 : 0 ≤ C) (hCD : C ≤ D) (hH : 0 ≤ 1 - H)
    (hsq : D ^ 2 + (1 - H) ^ 2 < 1) : tiltedBoxHeight C < H := by
  have hD0 : 0 ≤ D := hC0.trans hCD
  have hCC : C ^ 2 ≤ D ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hCD) (add_nonneg hC0 hD0)]
  have hrad : 0 ≤ 1 - C ^ 2 := by nlinarith [sq_nonneg (1 - H)]
  have hroot := Real.sq_sqrt hrad
  have hroot0 := Real.sqrt_nonneg (1 - C ^ 2)
  unfold tiltedBoxHeight
  by_contra hnlt
  have hle : Real.sqrt (1 - C ^ 2) ≤ 1 - H := by linarith
  have hprod := mul_nonneg (sub_nonneg.mpr hle)
    (add_nonneg hH hroot0)
  nlinarith

theorem tiltedBoxHeight_lt_thirty_three_hundredths {C : ℝ}
    (hC0 : 0 ≤ C) (hC : C ≤ 37 / 50) : tiltedBoxHeight C < 33 / 100 :=
  tiltedBoxHeight_lt_of_width_bound hC0 hC (by norm_num) (by norm_num)

theorem tiltedBoxHeight_lt_eight_twenty_fifths {C : ℝ}
    (hC0 : 0 ≤ C) (hC : C ≤ 73 / 100) : tiltedBoxHeight C < 8 / 25 :=
  tiltedBoxHeight_lt_of_width_bound hC0 hC (by norm_num) (by norm_num)

/-- IE8, including its narrow exact radius margin. -/
theorem initialFloorEnergyConditions_high_tilt
    {C B h : ℝ} (hC0 : 2 / 3 ≤ C) (hC : C ≤ 37 / 50)
    (hh0 : 21 / 100 ≤ h) (hh1 : h ≤ 17 / 50)
    (hBlo : -107 / 400 ≤ B)
    (hBhi : B ≤ -101 / 400 + 5 / 4 * h) :
    InitialFloorEnergyConditions (3 * C) B h := by
  have hB1 : B ≤ 107 / 400 := by linarith
  have hdsq : (3 * C) ^ 2 ≤ (111 / 50) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 111 / 50 - 3 * C by linarith)
      (show 0 ≤ 111 / 50 + 3 * C by linarith)]
  have hBsq : B ^ 2 ≤ (107 / 400) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ B + 107 / 400 by linarith)
      (show 0 ≤ 107 / 400 - B by linarith)]
  have htop : initialFloorTest (111 / 50) (-101 / 400 + 5 / 4 * h) h ≤ 4 :=
    initialFloorTest_affine_le_of_endpoint_bounds
      (l := 21 / 100) (r := 17 / 50) (sl := 61 / 100) (sr := 3 / 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) ⟨hh0, hh1⟩
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨by nlinarith, ?_⟩
  exact (initialFloorTest_mono_B hBhi (by linarith)).trans
    ((initialFloorTest_mono_d (by linarith) (by linarith)
      (by linarith) (show 3 * C ≤ 111 / 50 by linarith)).trans htop)

/-- FR's lower-width strip, using the actual nonnegative right niche
height and vanishing left niche height through the displayed interval. -/
theorem initialFloorEnergyConditions_middle_tilt_low_width
    {C B h : ℝ} (hC0 : 2 / 3 ≤ C) (hC : C ≤ 73 / 100)
    (hh0 : 1 / 20 ≤ h) (hh1 : h ≤ 21 / 100)
    (hBlo : -1 / 2 + 5 / 4 * h ≤ B)
    (hBhi : B ≤ -13 / 50 + 5 / 4 * h) :
    InitialFloorEnergyConditions (3 * C) B h := by
  have hB0 : -7 / 16 ≤ B := by linarith
  have hB1 : B ≤ 7 / 16 := by linarith
  have hdsq : (3 * C) ^ 2 ≤ (219 / 100) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 219 / 100 - 3 * C by linarith)
      (show 0 ≤ 219 / 100 + 3 * C by linarith)]
  have hBsq : B ^ 2 ≤ (7 / 16) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ B + 7 / 16 by linarith)
      (show 0 ≤ 7 / 16 - B by linarith)]
  have htop : initialFloorTest (219 / 100) (-13 / 50 + 5 / 4 * h) h ≤ 4 :=
    initialFloorTest_affine_le_of_endpoint_bounds
      (l := 1 / 20) (r := 21 / 100) (sl := 31 / 100) (sr := 61 / 100)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) ⟨hh0, hh1⟩
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨by nlinarith, ?_⟩
  exact (initialFloorTest_mono_B hBhi (by linarith)).trans
    ((initialFloorTest_mono_d (by linarith) (by linarith)
      (by linarith) (show 3 * C ≤ 219 / 100 by linarith)).trans htop)

theorem initialFloorEnergyConditions_high_tilt_of_endpoint_box
    {C h z w : ℝ} (hC0 : 2 / 3 ≤ C) (hC : C ≤ 37 / 50)
    (hh0 : 21 / 100 ≤ h) (hh1 : h ≤ 17 / 50)
    (hz0 : 0 ≤ z) (hz : z ≤ tiltedBoxHeight C)
    (hw0 : 0 ≤ w) (hw : w ≤ max (tiltedBoxHeight C - h) 0) :
    InitialFloorEnergyConditions (3 * C) (tiltedEndpointMomentum h z w) h := by
  have hH := tiltedBoxHeight_lt_thirty_three_hundredths (by linarith) hC
  have hw' : w ≤ 3 / 25 := hw.trans (max_le (by linarith) (by norm_num))
  apply initialFloorEnergyConditions_high_tilt hC0 hC hh0 hh1 <;>
    unfold tiltedEndpointMomentum <;> linarith

theorem initialFloorEnergyConditions_middle_tilt_low_width_of_endpoint_box
    {C h z : ℝ} (hC0 : 2 / 3 ≤ C) (hC : C ≤ 73 / 100)
    (hh0 : 1 / 20 ≤ h) (hh1 : h ≤ 21 / 100)
    (hz0 : 0 ≤ z) (hz : z ≤ tiltedBoxHeight C) :
    InitialFloorEnergyConditions (3 * C) (tiltedEndpointMomentum h z 0) h := by
  have hH := tiltedBoxHeight_lt_eight_twenty_fifths (by linarith) hC
  apply initialFloorEnergyConditions_middle_tilt_low_width hC0 hC hh0 hh1 <;>
    unfold tiltedEndpointMomentum <;> linarith

end AmbidextrousSofa.Analysis
