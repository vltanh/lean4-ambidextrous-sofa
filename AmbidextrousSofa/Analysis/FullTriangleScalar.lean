module

public import AmbidextrousSofa.Analysis.FullTriangleFloor
public import AmbidextrousSofa.Analysis.IntermediateTilt

@[expose] public section

/-!
# Scalar payment and global supporting plane for three full triangles

Every clipping term is retained. At an unclipped comparison point the
two tail squares are bounded by their displacement squares; the remaining
quadratic form is nonpositive even when the width varies, so the stationary
value at a comparison width bounds every larger width. A separate
positive-square payment combines the actual two exterior cuts and the
two complete niche gains.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

def fullTriangleDemand (a M h k c : ℝ) : ℝ :=
  (k + 2) * a + (k - 2) * M + 3 / 2 + 2 * k - 4 * c + h / 4

def fullTriangleRelaxation (a h k c u v : ℝ) : ℝ :=
  diagonalRelaxation a h k u v -
    (max (fullTriangleDemand a ((u + v) / 2) h k c) 0) ^ 2 / (2 + 3 * k)

def fullTriangleStationaryOffset (a k c : ℝ) : ℝ := (2 + 3 * k) * a / 2 - (4 * c - 2)

def fullTriangleBound (a h k c : ℝ) : ℝ :=
  a - (a - k) ^ 2 / 2 - k * h / 2 - h ^ 2 / 8 -
    (2 / 9) * (fullTriangleStationaryOffset a k c - (1 - k) * h / 4) ^ 2

def fullTriangleLoss (h k c : ℝ) : ℝ :=
  ((1 - k) / 2) *
    ((3 / 5 - (2 * c - (1 + k)) - h / 4) ^ 2 +
      (3 / 5 - (2 * c - (1 + k)) + 3 * h / 4) ^ 2)

theorem fullTriangle_square_payment {k S ZR ZL δR δL : ℝ}
    (hk : 0 < k) (hδR : 0 ≤ δR) (hδL : 0 ≤ δL)
    (hS : S ≤ ZR + ZL + (δR + δL) / 2) :
    (max S 0) ^ 2 / (2 + 3 * k) ≤
      (δR ^ 2 + δL ^ 2) / (2 * k) +
        ((max ZR 0) ^ 2 + (max ZL 0) ^ 2) / (1 + k) := by
  set x := max ZR 0
  set y := max ZL 0
  have hx : 0 ≤ x := le_max_right _ _
  have hy : 0 ≤ y := le_max_right _ _
  have hm : max S 0 ≤ x + y + (δR + δL) / 2 :=
    max_le (by linarith only [hS, le_max_left ZR 0, le_max_left ZL 0]) (by positivity)
  have hkr : 0 ≤ k * (1 + k) := by positivity
  rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
    (by positivity)]
  linarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_max_right S 0) hm 2) hkr,
    mul_nonneg hkr (sq_nonneg (x - y)), mul_nonneg hkr (sq_nonneg (δR - δL)),
    sq_nonneg (k * x - (1 + k) * δR), sq_nonneg (k * x - (1 + k) * δL),
    sq_nonneg (k * y - (1 + k) * δR), sq_nonneg (k * y - (1 + k) * δL)]

theorem fullTriangleRelaxation_le_joint_tangent {a h k c u v a0 u0 v0 : ℝ}
    (hk : 0 < k) (hq : 0 ≤ (u + v - h) / 2 - k)
    (hu0 : u0 ≤ k + a0 / 2) (hv0 : v0 ≤ h + k + a0 / 2)
    (hS0 : 0 ≤ fullTriangleDemand a0 ((u0 + v0) / 2) h k c) :
    let S0 := fullTriangleDemand a0 ((u0 + v0) / 2) h k c
    fullTriangleRelaxation a h k c u v ≤
      a0 - ((a0 - u0) ^ 2 + (a0 - v0) ^ 2) / 2 - a0 * h / 2 -
        ((u0 + v0 - h) / 2 - k) ^ 2 - S0 ^ 2 / (2 + 3 * k) +
      (1 - h / 2 - (2 * a0 - u0 - v0) - 2 * S0 * (k + 2) / (2 + 3 * k)) * (a - a0) +
      (a0 - u0 - ((u0 + v0 - h) / 2 - k) - S0 * (k - 2) / (2 + 3 * k)) * (u - u0) +
      (a0 - v0 - ((u0 + v0 - h) / 2 - k) - S0 * (k - 2) / (2 + 3 * k)) * (v - v0) := by
  have hclipR := shifted_positive_square_le_displacement (u - a / 2)
    (show u0 - a0 / 2 ≤ k by linarith only [hu0])
  have hclipL := shifted_positive_square_le_displacement (v - a / 2)
    (show v0 - a0 / 2 ≤ h + k by linarith only [hv0])
  rw [show u - a / 2 - k = u - k - a / 2 by ring] at hclipR
  rw [show v - a / 2 - (h + k) = v - h - k - a / 2 by ring] at hclipL
  have hS := mul_le_mul_of_nonneg_right (positive_square_ge_tangent
    (fullTriangleDemand a ((u + v) / 2) h k c) hS0)
    (inv_nonneg.2 (by linarith only [hk] : 0 ≤ 2 + 3 * k))
  rw [fullTriangleRelaxation, diagonalRelaxation, max_eq_left hq]
  simp only [fullTriangleDemand, div_eq_mul_inv _ (2 + 3 * k)] at hS ⊢
  linarith only [hclipR, hclipL, hS, sq_nonneg (a - a0),
    sq_nonneg ((u - u0 + (v - v0)) / 2 - (a - a0) / 2)]

theorem fullTriangle_stationary_offset_bounds {k c : ℝ}
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70)
    (hc0 : 923 / 1000 < c) (hc1 : c < 231 / 250) :
    703 / 1000 < fullTriangleStationaryOffset (37 / 25) k c ∧
      fullTriangleStationaryOffset (37 / 25) k c < 71 / 100 := by
  rw [fullTriangleStationaryOffset]
  constructor <;> linarith only [hk0, hk1, hc0, hc1]

/-- At an unclipped point and every width `a ≥ a0`, the relaxation is at most its value at the
stationary comparison point of width `a0`. -/
theorem fullTriangleRelaxation_le_bound {a a0 h k c u v : ℝ}
    (ha : a0 ≤ a) (ha0 : 73 / 50 ≤ a0) (hh0 : 0 ≤ h) (hh1 : h ≤ 17 / 50)
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hs0 : 2 / 3 < fullTriangleStationaryOffset a0 k c)
    (hs1 : fullTriangleStationaryOffset a0 k c < 71 / 100)
    (hq : 0 ≤ (u + v - h) / 2 - k) :
    fullTriangleRelaxation a h k c u v ≤ fullTriangleBound a0 h k c := by
  have hd : 0 < 2 + 3 * k := by linarith only [hk0]
  rw [fullTriangleBound]
  generalize hz : fullTriangleStationaryOffset a0 k c - (1 - k) * h / 4 = z
  have hz0 : 0 < z := by
    linarith only [hz, hs0, hh0, hh1, mul_le_mul_of_nonneg_right hk0.le hh0]
  have hzb : (2 - k) * z < 8 / 5 * (71 / 100) - 3 / 4 * h / 4 := by
    rw [← hz]
    linarith only [mul_le_mul_of_nonneg_right
      (show 3 / 4 ≤ (2 - k) * (1 - k) by linarith only [hksq, hk1]) hh0,
      mul_pos (sub_pos.2 hk0) (sub_pos.2 hs0), hs1, hk0]
  obtain ⟨m, hm⟩ : ∃ m, m = (a0 + k) / 2 + (2 - k) * z / 9 + h / 4 := ⟨_, rfl⟩
  have hS : fullTriangleDemand a0 ((m + m) / 2) h k c = 2 * (2 + 3 * k) * z / 9 := by
    rw [fullTriangleDemand, hm]
    rw [fullTriangleStationaryOffset] at hz
    linear_combination hz + (1 / 2 - z / 9) * hksq
  have htan := fullTriangleRelaxation_le_joint_tangent (a := a) (c := c) (a0 := a0)
    (u0 := m) (v0 := m) (by linarith only [hk0]) hq
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
    (by linarith only [mul_pos hd hz0, hk1, ha0] : 1 + k - a0 - 2 * (2 + 3 * k) * z / 9 ≤ 0)
    (sub_nonneg.2 ha)

theorem fullTriangleRelaxation_add_loss_lt {a h k c u v : ℝ}
    (ha : 37 / 25 ≤ a) (hh0 : 0 ≤ h) (hh1 : h ≤ 17 / 50)
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hc0 : 923 / 1000 < c) (hc1 : c < 231 / 250)
    (hq : 0 ≤ (u + v - h) / 2 - k) :
    fullTriangleRelaxation a h k c u v + fullTriangleLoss h k c < (41 / 50 : ℝ) := by
  obtain ⟨hs0, hs1⟩ := fullTriangle_stationary_offset_bounds hk0 hk1 hc0 hc1
  have hbound := fullTriangleRelaxation_le_bound ha (by norm_num) hh0 hh1 hk0 hk1 hksq
    (by linarith only [hs0]) hs1 hq
  rw [fullTriangleBound] at hbound
  rw [fullTriangleLoss]
  generalize fullTriangleStationaryOffset (37 / 25) k c = s at hs0 hs1 hbound
  generalize hd : 3 / 5 - (2 * c - (1 + k)) = d
  have hd0 : 0 < d := by linarith only [hd, hc1, hk0]
  have hd1 : d < 589 / 3500 := by linarith only [hd, hc0, hk1]
  have hell : -k / 2 + (1 - k) * s / 9 + (1 - k) / 2 * d < -1 / 10 := by
    linarith only [mul_pos (sub_pos.2 hk0) (sub_pos.2 hs0), mul_pos (sub_pos.2 hk0) hd0, hs1,
      hd1, hk0]
  have hq' : -1 / 8 - (1 - k) ^ 2 / 72 + 5 * ((1 - k) / 2) / 8 < 1 / 16 := by
    linarith only [hksq, hk0]
  linarith only [hbound, hksq, hk1, hh0, mul_le_mul_of_nonneg_right hell.le hh0,
    mul_le_mul_of_nonneg_right hq'.le (sq_nonneg h), mul_nonneg hh0 (sub_nonneg.2 hh1),
    mul_pos (sub_pos.2 hs0) (by linarith only [hs0] : 0 < s + 703 / 1000),
    mul_le_mul_of_nonneg_right (by linarith only [hk0] : 1 - k ≤ 3 / 5) (sq_nonneg d),
    mul_pos (sub_pos.2 hd1) (by linarith only [hd0] : 0 < 589 / 3500 + d)]

end AmbidextrousSofa
