module

public import AmbidextrousSofa.Analysis.FullTriangleScalar

@[expose] public section

/-!
# The sharper triangle bound in the remaining tilted strip

The complete jointly concave support relaxation is compared at width
`73/50`. Actual zero left endpoint niche later supplies the asymmetric
floor correction. All clipping cases remain present in the relaxation;
the comparison point alone is unclipped. Every numerical margin below
is rational and every radical is kept symbolic.
-/

noncomputable section

namespace AmbidextrousSofa

def tiltedTriangleLoss (h k c : ℝ) : ℝ :=
  ((1 - k) / 2) *
    ((1 / 2 - (2 * c - (1 + k)) - h / 4) ^ 2 +
      (1 / 2 - (2 * c - (1 + k)) + 1 / 12 + 3 * h / 4) ^ 2)

theorem tiltedTriangle_stationary_offset_bounds {k c : ℝ}
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70)
    (hc0 : 923 / 1000 < c) (hc1 : c < 231 / 250) :
    2 / 3 < fullTriangleStationaryOffset (73 / 50) k c ∧
      fullTriangleStationaryOffset (73 / 50) k c < 7 / 10 := by
  rw [fullTriangleStationaryOffset]
  constructor <;> linarith only [hk0, hk1, hc0, hc1]

/-- The asymmetric floor correction and the stationary value decrease
from height `1/20` throughout the entire remaining medium-tilt strip. -/
theorem tiltedTriangleRelaxation_add_loss_lt {a h k c u v : ℝ}
    (ha : 73 / 50 ≤ a) (hh0 : 1 / 20 ≤ h) (hh1 : h ≤ 21 / 100)
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hc0 : 923 / 1000 < c) (hc1 : c < 231 / 250)
    (hq : 0 ≤ (u + v - h) / 2 - k) :
    fullTriangleRelaxation a h k c u v + tiltedTriangleLoss h k c < (41 / 50 : ℝ) := by
  obtain ⟨hs0, hs1⟩ := tiltedTriangle_stationary_offset_bounds hk0 hk1 hc0 hc1
  have hbound := fullTriangleRelaxation_le_bound ha (by norm_num) (by linarith only [hh0])
    (by linarith only [hh1]) hk0 hk1 hksq hs0 (by linarith only [hs1]) hq
  rw [fullTriangleBound] at hbound
  rw [tiltedTriangleLoss]
  generalize hs : fullTriangleStationaryOffset (73 / 50) k c = s at hs0 hs1 hbound
  rw [fullTriangleStationaryOffset] at hs
  generalize hD : 1 / 2 - (2 * c - (1 + k)) = D
  have hD0 : 21 / 400 < D := by linarith only [hD, hc1, hk0]
  have hD1 : D < 239 / 3500 := by linarith only [hD, hc0, hk1]
  have hz : 53 / 80 < s - (1 - k) / 80 := by linarith only [hs, hk0, hc1]
  have hell : -k / 2 + (1 - k) * s / 9 + (1 - k) / 2 * (D + 1 / 8) < -9 / 100 := by
    linarith only [mul_pos (sub_pos.2 hk0) (sub_pos.2 hs0), mul_pos (sub_pos.2 hk0)
      (sub_pos.2 hD0), hs1, hD1, hk0]
  have hq' : -1 / 8 - (1 - k) ^ 2 / 72 + 5 * ((1 - k) / 2) / 8 < 1 / 16 := by
    linarith only [hksq, hk0]
  -- The bound is `F (1/20) + ℓ (h - 1/20) + q (h² - 1/20²)` with slope `ℓ` and curvature `q`.
  linarith only [hbound, hksq, hk1, hh0, mul_le_mul_of_nonneg_right hell.le (sub_nonneg.2 hh0),
    mul_le_mul_of_nonneg_right hq'.le
      (mul_nonneg (sub_nonneg.2 hh0) (by linarith only [hh0] : (0 : ℝ) ≤ h + 1 / 20)),
    mul_nonneg (sub_nonneg.2 hh0) (sub_nonneg.2 hh1),
    mul_pos (sub_pos.2 hz) (by linarith only [hz] : 0 < s - (1 - k) / 80 + 53 / 80),
    mul_le_mul_of_nonneg_right (by linarith only [hk0] : (1 - k) / 2 ≤ 3 / 10)
      (add_nonneg (sq_nonneg (D - 1 / 80)) (sq_nonneg (D + 1 / 12 + 3 / 80))),
    mul_pos (by linarith only [hD1] : 0 < 7 / 125 - (D - 1 / 80))
      (by linarith only [hD0] : 0 < 7 / 125 + (D - 1 / 80)),
    mul_pos (by linarith only [hD1] : 0 < 19 / 100 - (D + 1 / 12 + 3 / 80))
      (by linarith only [hD0] : 0 < 19 / 100 + (D + 1 / 12 + 3 / 80))]

end AmbidextrousSofa
