module

public import AmbidextrousSofa.Analysis.TiltedInitialEnergy
public import AmbidextrousSofa.Analysis.TiltedRadiusWidth

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

attribute [local simp]
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
    (hd : 0 ≤ d) (hlr : l < r) (hh : h ∈ Icc l r)
    (hsl : sl ^ 2 ≤ l * (2 - l)) (hsr : sr ^ 2 ≤ r * (2 - r))
    (hleft : d ^ 2 + (A + 5 / 4 * l) ^ 2 +
      (A + 5 / 4 * l) * (1 - l) - d * sl ≤ K)
    (hright : d ^ 2 + (A + 5 / 4 * r) ^ 2 +
      (A + 5 / 4 * r) * (1 - r) - d * sr ≤ K) :
    initialFloorTest d (A + 5 / 4 * h) h ≤ K := by
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

/-- A dry low endpoint makes one radius-defined width sufficient for
both initial-floor tests, throughout the whole nonsmall height interval. -/
theorem initialFloorEnergyConditions_of_radius_width
    {C h z : ℝ} (hC0 : 2 / 3 ≤ C) (hC : C ≤ tiltedRadiusWidth)
    (hh0 : tiltedBalanceHeight ≤ h) (hh1 : h ≤ 1 / 3)
    (hz0 : 0 ≤ z) (hz : z ≤ tiltedBoxHeight C) :
    InitialFloorEnergyConditions (3 * C) (tiltedEndpointMomentum h z 0) h := by
  have hCsq : 9 * C ^ 2 ≤ 5 - tiltedRadiusMomentum ^ 2 := by
    have hpow := pow_le_pow_left₀ (by linarith : 0 ≤ C) hC 2
    nlinarith [tiltedRadiusWidth_sq]
  have hhroot := tiltedBalanceHeight_mem
  have hH : tiltedBoxHeight C ≤ 1 / 3 := by
    have hroot : (2 / 3 : ℝ) ≤ Real.sqrt (1 - C ^ 2) :=
      Real.le_sqrt_of_sq_le (by nlinarith only [hCsq, sq_nonneg tiltedRadiusMomentum])
    unfold tiltedBoxHeight
    linarith only [hroot]
  have hz1 : z ≤ 1 / 3 := hz.trans hH
  have hBlo : tiltedRadiusMomentum ≤ tiltedEndpointMomentum h z 0 := by
    unfold tiltedRadiusMomentum tiltedBalanceMomentum tiltedEndpointMomentum
    linarith only [hh0, hz0]
  have hBhi : tiltedEndpointMomentum h z 0 ≤ -tiltedRadiusMomentum := by
    have hroot := tiltedBalanceHeight_bounds.2
    norm_num at hroot
    unfold tiltedRadiusMomentum tiltedBalanceMomentum tiltedEndpointMomentum
    linarith only [hroot, hh1, hz1]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hBlo) (sub_nonneg.mpr hBhi)]
  have hD : 3 * C ≤ Real.sqrt tiltedRadiusSquare := by
    unfold tiltedRadiusWidth at hC
    linarith only [hC]
  have hd : (0 : ℝ) ≤ Real.sqrt tiltedRadiusSquare := Real.sqrt_nonneg _
  have hhi : tiltedEndpointMomentum h z 0 ≤ -1 / 4 + 5 / 4 * h := by
    unfold tiltedEndpointMomentum
    linarith only [hz1]
  have hmono : 0 ≤ tiltedEndpointMomentum h z 0 + (-1 / 4 + 5 / 4 * h) + 1 - h := by
    unfold tiltedEndpointMomentum
    linarith only [hz0, hh0, hhroot.1]
  have hrange : tiltedBalanceHeight < 1 / 3 :=
    tiltedBalanceHeight_bounds.2.trans_lt (by norm_num)
  have hleft : tiltedRadiusSquare + (-1 / 4 + 5 / 4 * tiltedBalanceHeight) ^ 2 +
      (-1 / 4 + 5 / 4 * tiltedBalanceHeight) * (1 - tiltedBalanceHeight) -
      Real.sqrt tiltedRadiusSquare * initialFloorSine tiltedBalanceHeight ≤ 4 := by
    have h := tiltedBalanceHeight_energy_eq.le
    have hb : tiltedBalanceMomentum tiltedBalanceHeight + 1 / 4 =
        -1 / 4 + 5 / 4 * tiltedBalanceHeight := by dsimp [tiltedBalanceMomentum]; ring
    rw [hb] at h
    exact h
  have hright : initialFloorTest (Real.sqrt tiltedRadiusSquare) (-1 / 4 + 5 / 4 * (1 / 3)) (1 / 3) ≤ 4 := by
    have hr2 : 2 ≤ Real.sqrt tiltedRadiusSquare := by linarith only [hC0, hD]
    have hr5 : (Real.sqrt tiltedRadiusSquare) ^ 2 ≤ 5 := by
      rw [Real.sq_sqrt tiltedRadiusSquare_pos.le]
      unfold tiltedRadiusSquare
      linarith only [sq_nonneg tiltedRadiusMomentum]
    have hs2 : (2 / 3 : ℝ) ≤ initialFloorSine (1 / 3) :=
      Real.le_sqrt_of_sq_le (by norm_num)
    have hprod := mul_le_mul_of_nonneg_right hs2 hd
    unfold initialFloorTest
    norm_num
    linarith only [hr2, hr5, hprod]
  exact (initialFloorTest_mono_B hhi hmono).trans
    ((initialFloorTest_mono_d (by linarith only [hh0, hhroot.1]) (by linarith only [hh1])
      (by linarith only [hC0]) hD).trans
      (initialFloorTest_affine_le_of_endpoint_bounds (l := tiltedBalanceHeight) (r := 1 / 3)
        (sl := initialFloorSine tiltedBalanceHeight) (sr := initialFloorSine (1 / 3)) hd hrange
        ⟨hh0, hh1⟩ (initialFloorSine_sq hhroot.1 (by linarith only [hhroot.2])).le
        (initialFloorSine_sq (by norm_num) (by norm_num)).le
        (by rw [Real.sq_sqrt tiltedRadiusSquare_pos.le]; exact hleft) hright))

end AmbidextrousSofa.Analysis
