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
    {x y sx sy w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hsx : sx ^ 2 ≤ x * (2 - x)) (hsy : sy ^ 2 ≤ y * (2 - y)) :
    (1 - w) * sx + w * sy ≤ initialFloorSine ((1 - w) * x + w * y) := by
  have hw : 0 ≤ 1 - w := sub_nonneg.mpr hw1
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  linarith [mul_nonneg hw (sub_nonneg.mpr hsx), mul_nonneg hw0 (sub_nonneg.mpr hsy),
    mul_nonneg (mul_nonneg hw0 hw) (add_nonneg (sq_nonneg (x - y)) (sq_nonneg (sx - sy)))]

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
  have _ := And.intro hl hr -- not needed by the proof; they stay in the statement for the callers
  have hrl : 0 < r - l := sub_pos.mpr hlr
  -- write `h` as the convex combination `(1 - w) * l + w * r`
  obtain ⟨w, hw0, hw1, rfl⟩ : ∃ w, 0 ≤ w ∧ w ≤ 1 ∧ h = (1 - w) * l + w * r :=
    ⟨(h - l) / (r - l), div_nonneg (by linarith [hh.1]) hrl.le,
      (div_le_one₀ hrl).2 (by linarith [hh.2]), by field_simp; ring⟩
  unfold initialFloorTest
  linarith [mul_le_mul_of_nonneg_left (initialFloorSine_convex_comb_lower hw0 hw1 hsl hsr) hd,
    mul_le_mul_of_nonneg_left hleft (sub_nonneg.mpr hw1), mul_le_mul_of_nonneg_left hright hw0,
    mul_nonneg (mul_nonneg hw0 (sub_nonneg.mpr hw1)) (sq_nonneg (r - l))]

theorem initialFloorTest_mono_d {d D B h : ℝ}
    (h0 : 0 ≤ h) (h2 : h ≤ 2) (hd : 1 / 2 ≤ d) (hdD : d ≤ D) :
    initialFloorTest d B h ≤ initialFloorTest D B h := by
  unfold initialFloorTest
  linarith [mul_nonneg (sub_nonneg.mpr hdD)
    (show 0 ≤ D + d - initialFloorSine h by linarith [initialFloorSine_le_one h0 h2])]

theorem initialFloorTest_mono_B {d B U h : ℝ}
    (hBU : B ≤ U) (hsum : 0 ≤ B + U + 1 - h) :
    initialFloorTest d B h ≤ initialFloorTest d U h := by
  unfold initialFloorTest
  linarith [mul_nonneg (sub_nonneg.mpr hBU) hsum]

theorem tiltedBoxHeight_lt_of_width_bound {C D H : ℝ}
    (hC0 : 0 ≤ C) (hCD : C ≤ D) (hsq : D ^ 2 + (1 - H) ^ 2 < 1) : tiltedBoxHeight C < H := by
  have := Real.lt_sqrt_of_sq_lt
    (show (1 - H) ^ 2 < 1 - C ^ 2 by linarith [pow_le_pow_left₀ hC0 hCD 2])
  unfold tiltedBoxHeight
  linarith

theorem tiltedBoxHeight_lt_thirty_three_hundredths {C : ℝ}
    (hC0 : 0 ≤ C) (hC : C ≤ 37 / 50) : tiltedBoxHeight C < 33 / 100 :=
  tiltedBoxHeight_lt_of_width_bound hC0 hC (by norm_num)

/-- IE8, including its narrow exact radius margin. -/
theorem initialFloorEnergyConditions_high_tilt
    {C B h : ℝ} (hC0 : 2 / 3 ≤ C) (hC : C ≤ 37 / 50)
    (hh0 : 21 / 100 ≤ h) (hh1 : h ≤ 17 / 50)
    (hBlo : -107 / 400 ≤ B)
    (hBhi : B ≤ -101 / 400 + 5 / 4 * h) :
    InitialFloorEnergyConditions (3 * C) B h := by
  constructor
  · linarith [mul_nonneg (show 0 ≤ 111 / 50 - 3 * C by linarith)
      (show 0 ≤ 111 / 50 + 3 * C by linarith), mul_nonneg (show 0 ≤ B + 107 / 400 by linarith)
      (show 0 ≤ 107 / 400 - B by linarith)]
  exact (initialFloorTest_mono_B hBhi (by linarith)).trans
    ((initialFloorTest_mono_d (by linarith) (by linarith) (by linarith)
      (show 3 * C ≤ 111 / 50 by linarith)).trans
      (initialFloorTest_affine_le_of_endpoint_bounds
        (l := 21 / 100) (r := 17 / 50) (sl := 61 / 100) (sr := 3 / 4)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) ⟨hh0, hh1⟩
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)))

/-- FR's lower-width strip, using the actual nonnegative right niche
height and vanishing left niche height through the displayed interval. -/
theorem initialFloorEnergyConditions_middle_tilt_low_width
    {C B h : ℝ} (hC0 : 2 / 3 ≤ C) (hC : C ≤ 73 / 100)
    (hh0 : 1 / 20 ≤ h) (hh1 : h ≤ 21 / 100)
    (hBlo : -1 / 2 + 5 / 4 * h ≤ B)
    (hBhi : B ≤ -13 / 50 + 5 / 4 * h) :
    InitialFloorEnergyConditions (3 * C) B h := by
  constructor
  · linarith [mul_nonneg (show 0 ≤ 219 / 100 - 3 * C by linarith)
      (show 0 ≤ 219 / 100 + 3 * C by linarith), mul_nonneg (show 0 ≤ B + 7 / 16 by linarith)
      (show 0 ≤ 7 / 16 - B by linarith)]
  exact (initialFloorTest_mono_B hBhi (by linarith)).trans
    ((initialFloorTest_mono_d (by linarith) (by linarith) (by linarith)
      (show 3 * C ≤ 219 / 100 by linarith)).trans
      (initialFloorTest_affine_le_of_endpoint_bounds
        (l := 1 / 20) (r := 21 / 100) (sl := 31 / 100) (sr := 61 / 100)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) ⟨hh0, hh1⟩
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)))

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
  have hH : tiltedBoxHeight C < 8 / 25 :=
    tiltedBoxHeight_lt_of_width_bound (by linarith) hC (by norm_num)
  apply initialFloorEnergyConditions_middle_tilt_low_width hC0 hC hh0 hh1 <;>
    unfold tiltedEndpointMomentum <;> linarith

end AmbidextrousSofa.Analysis
