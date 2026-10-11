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

theorem tiltedTriangleRelaxation_le_bound {a h k c u v : ℝ}
    (ha : 73 / 50 ≤ a) (hh0 : 0 ≤ h) (hh1 : h ≤ 21 / 100)
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hc0 : 923 / 1000 < c) (hc1 : c < 231 / 250)
    (hq : 0 ≤ (u + v - h) / 2 - k) :
    fullTriangleRelaxation a h k c u v ≤ fullTriangleBound (73 / 50) h k c := by
  obtain ⟨hs0, hs1⟩ := tiltedTriangle_stationary_offset_bounds hk0 hk1 hc0 hc1
  have hd : 0 < 2 + 3 * k := by linarith only [hk0]
  rw [fullTriangleBound]
  generalize hz : fullTriangleStationaryOffset (73 / 50) k c - (1 - k) * h / 4 = z
  have hz0 : 0 < z := by
    linarith only [hz, hs0, hh0, hh1, mul_le_mul_of_nonneg_right hk0.le hh0]
  have hzb : (2 - k) * z < 8 / 5 * (7 / 10) - 3 / 4 * h / 4 := by
    rw [← hz]
    linarith only [mul_le_mul_of_nonneg_right
      (show 3 / 4 ≤ (2 - k) * (1 - k) by linarith only [hksq, hk1]) hh0,
      mul_pos (sub_pos.2 hk0) (sub_pos.2 hs0), hs1, hk0]
  obtain ⟨m, hm⟩ : ∃ m, m = (73 / 50 + k) / 2 + (2 - k) * z / 9 + h / 4 := ⟨_, rfl⟩
  have hS : fullTriangleDemand (73 / 50) ((m + m) / 2) h k c = 2 * (2 + 3 * k) * z / 9 := by
    rw [fullTriangleDemand, hm]
    rw [fullTriangleStationaryOffset] at hz
    linear_combination hz + (1 / 2 - z / 9) * hksq
  have htan := fullTriangleRelaxation_le_joint_tangent (a := a) (c := c) (a0 := 73 / 50)
    (u0 := m) (v0 := m) (by linarith only [hk0]) hq
    (by linarith only [hm, mul_pos (by linarith only [hk1] : (0 : ℝ) < 2 - k) hz0, hk1, hh1])
    (by linarith only [hm, hzb, hk0, hh1]) (by linarith only [hm, hzb, hk0, hh0, hh1])
    (by rw [hS]; positivity)
  dsimp only at htan
  rw [hS] at htan
  refine htan.trans ?_
  have e1 : (2 * (2 + 3 * k) * z / 9) ^ 2 / (2 + 3 * k) = 4 * (2 + 3 * k) * z ^ 2 / 81 := by
    field_simp; ring
  have e2 : 2 * (2 * (2 + 3 * k) * z / 9) * (k + 2) / (2 + 3 * k) = 4 * z * (k + 2) / 9 := by
    field_simp; ring
  have e3 : 2 * (2 + 3 * k) * z / 9 * (k - 2) / (2 + 3 * k) = 2 * z * (k - 2) / 9 := by
    field_simp
  rw [e1, e2, e3, hm]
  linear_combination (-2 / 81 * z ^ 2) * hksq + mul_nonpos_of_nonpos_of_nonneg
    (by linarith only [mul_pos hd hz0, hk1] : 1 + k - 73 / 50 - 2 * (2 + 3 * k) * z / 9 ≤ 0)
    (sub_nonneg.2 ha)

/-- The asymmetric floor correction and the stationary value decrease
from height `1/20` throughout the entire remaining medium-tilt strip. -/
theorem tiltedTriangleRelaxation_add_loss_lt {a h k c u v : ℝ}
    (ha : 73 / 50 ≤ a) (hh0 : 1 / 20 ≤ h) (hh1 : h ≤ 21 / 100)
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hc0 : 923 / 1000 < c) (hc1 : c < 231 / 250)
    (hq : 0 ≤ (u + v - h) / 2 - k) :
    fullTriangleRelaxation a h k c u v + tiltedTriangleLoss h k c < (41 / 50 : ℝ) := by
  have hbound := tiltedTriangleRelaxation_le_bound ha (by linarith only [hh0]) hh1
    hk0 hk1 hksq hc0 hc1 hq
  obtain ⟨hs0, hs1⟩ := tiltedTriangle_stationary_offset_bounds hk0 hk1 hc0 hc1
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
