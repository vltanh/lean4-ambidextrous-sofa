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
two complete niche gains. All three floor corrections share a tilt payment
and a comparison of the complete score at a Newton-generated parameter corner.
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

/-- The three-triangle bound follows from stationarity, the two clipping
conditions, and a nonpositive width derivative. No numerical width or tilt
cutoff is part of this comparison. -/
theorem fullTriangleRelaxation_le_stationary_bound {a a0 h k c u v : ℝ}
    (ha : a0 ≤ a) (hk : 0 < k) (hksq : k ^ 2 + 2 * k = 1)
    (hq : 0 ≤ (u + v - h) / 2 - k)
    (hz : 0 ≤ fullTriangleStationaryOffset a0 k c - (1 - k) * h / 4)
    (hclipR : (a0 + k) / 2 + (2 - k) *
      (fullTriangleStationaryOffset a0 k c - (1 - k) * h / 4) / 9 + h / 4 ≤ k + a0 / 2)
    (hclipL : (a0 + k) / 2 + (2 - k) *
      (fullTriangleStationaryOffset a0 k c - (1 - k) * h / 4) / 9 + h / 4 ≤ h + k + a0 / 2)
    (hslope : 1 + k - a0 - 2 * (2 + 3 * k) *
      (fullTriangleStationaryOffset a0 k c - (1 - k) * h / 4) / 9 ≤ 0) :
    fullTriangleRelaxation a h k c u v ≤ fullTriangleBound a0 h k c := by
  set z := fullTriangleStationaryOffset a0 k c - (1 - k) * h / 4 with hzdef
  set m := (a0 + k) / 2 + (2 - k) * z / 9 + h / 4 with hm
  have hd : 0 < 2 + 3 * k := by linarith
  have hS : fullTriangleDemand a0 ((m + m) / 2) h k c = 2 * (2 + 3 * k) * z / 9 := by
    rw [fullTriangleDemand, hm]
    rw [fullTriangleStationaryOffset] at hzdef
    linear_combination -hzdef + (1 / 2 - z / 9) * hksq
  have htan := fullTriangleRelaxation_le_joint_tangent (a := a) (c := c) (a0 := a0)
    (u0 := m) (v0 := m) hk hq hclipR hclipL (by rw [hS]; positivity)
  dsimp only at htan
  rw [hS] at htan
  refine htan.trans ?_
  have e1 : (2 * (2 + 3 * k) * z / 9) ^ 2 / (2 + 3 * k) = 4 * (2 + 3 * k) * z ^ 2 / 81 := by
    field_simp; ring
  have e2 : 2 * (2 * (2 + 3 * k) * z / 9) * (k + 2) / (2 + 3 * k) = 4 * z * (k + 2) / 9 := by
    field_simp; ring
  have e3 : 2 * (2 + 3 * k) * z / 9 * (k - 2) / (2 + 3 * k) = 2 * z * (k - 2) / 9 := by
    field_simp
  rw [e1, e2, e3, hm, fullTriangleBound, ← hzdef]
  linear_combination (-2 / 81 * z ^ 2) * hksq +
    mul_nonpos_of_nonpos_of_nonneg hslope (sub_nonneg.2 ha)

/-- At an unclipped point and every width `a ≥ a0`, the relaxation is at most its value at the
stationary comparison point of width `a0`. -/
theorem fullTriangleRelaxation_le_bound {a a0 h k c u v : ℝ}
    (ha : a0 ≤ a) (ha0 : 73 / 50 ≤ a0) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 3)
    (hk0 : diagonalOffsetLower < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hs0 : 2 / 3 < fullTriangleStationaryOffset a0 k c)
    (hs1 : fullTriangleStationaryOffset a0 k c < 71 / 100)
    (hq : 0 ≤ (u + v - h) / 2 - k) :
    fullTriangleRelaxation a h k c u v ≤ fullTriangleBound a0 h k c := by
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
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
  rw [← hz, ← fullTriangleBound]
  apply fullTriangleRelaxation_le_stationary_bound ha (by linarith only [hk0]) hksq hq
    (by rw [hz]; exact hz0.le)
  · rw [hz]
    linarith only [hzb, hk0, hh1]
  · rw [hz]
    linarith only [hzb, hk0, hh0, hh1]
  · rw [hz]
    linarith only [mul_pos hd hz0, hk1, ha0]

/-- The same height payment for two floor squares, including a missing square. -/
theorem triangle_tilt_payment {k s p q r t h h0 : ℝ}
    (hk : 2 / 5 ≤ k) (hk1 : k ≤ 1) (hs : s ≤ 3 / 4)
    (hp : r * p + t * q ≤ 1 / 6) (hm : r ^ 2 + t ^ 2 ≤ 5 / 8)
    (hh : h0 ≤ h) (hh0 : 0 ≤ h0) (hh1 : h + h0 ≤ 1 / 2) :
    -k * h / 2 - h ^ 2 / 8 - (2 / 9) * (s - (1 - k) * h / 4) ^ 2 +
        ((1 - k) / 2) * ((p + r * h) ^ 2 + (q + t * h) ^ 2) ≤
      -k * h0 / 2 - h0 ^ 2 / 8 - (2 / 9) * (s - (1 - k) * h0 / 4) ^ 2 +
        ((1 - k) / 2) * ((p + r * h0) ^ 2 + (q + t * h0) ^ 2) := by
  have hA : 0 ≤ 1 - k := by linarith
  have hL : -k / 2 + (1 - k) * s / 9 + (1 - k) * (r * p + t * q) ≤ -1 / 20 := by
    nlinarith [mul_le_mul_of_nonneg_left hs hA, mul_le_mul_of_nonneg_left hp hA]
  have hQ : -1 / 8 - (1 - k) ^ 2 / 72 + (1 - k) / 2 * (r ^ 2 + t ^ 2) ≤ 1 / 16 := by
    nlinarith [mul_le_mul_of_nonneg_left hm hA, sq_nonneg (1 - k)]
  have hH : 0 ≤ h ^ 2 - h0 ^ 2 := by nlinarith
  linarith only [hh, mul_le_mul_of_nonneg_right hL (sub_nonneg.2 hh),
    mul_le_mul_of_nonneg_right hQ hH,
    mul_nonneg (sub_nonneg.2 hh) (sub_nonneg.2 hh1)]

/-- The score after using the diagonal's quadratic identity. -/
def triangleCornerScore (a h k c bR bL w : ℝ) : ℝ :=
  (a + 1 - h / 2) * k + a - a ^ 2 / 2 - 1 / 2 - h ^ 2 / 8 -
    (2 / 9) * (fullTriangleStationaryOffset a k c - (1 - k) * h / 4) ^ 2 +
    ((1 - k) / 2) * (w * (bR - (2 * c - (1 + k))) ^ 2 +
      (bL - (2 * c - (1 + k))) ^ 2)

-- Compare cosine first. The floor payment drops, but the larger stationary
-- square drops more; a difference of squares keeps both effects together.
theorem triangleCornerScore_mono_cos {a h k c C bR bL w : ℝ}
    (hc : c ≤ C) (hk : 2 / 5 ≤ k) (hk1 : k ≤ 1)
    (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hz : 3 / 5 ≤ fullTriangleStationaryOffset a k C - (1 - k) * h / 4)
    (hR : bR - (2 * c - (1 + k)) ≤ 1 / 4)
    (hL : bL - (2 * c - (1 + k)) ≤ 1 / 4) :
    triangleCornerScore a h k c bR bL w ≤ triangleCornerScore a h k C bR bL w := by
  set d := C - c
  set z := fullTriangleStationaryOffset a k C - (1 - k) * h / 4
  set p := bR - (2 * c - (1 + k))
  set q := bL - (2 * c - (1 + k))
  have hd : 0 ≤ d := sub_nonneg.2 hc
  have hA : 0 ≤ 1 - k := by linarith
  have hwp : w * p ≤ 1 / 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hR hw]
  have hloss : (1 - k) * (w * p + q) ≤ 3 / 10 := by
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hwp hL) hA]
  have hz' : 3 / 5 ≤ z := hz
  have hgain : 0 ≤ 16 * z / 9 - 2 * (1 - k) * (w * p + q) := by linarith
  unfold triangleCornerScore
  dsimp [d, z, p, q] at *
  unfold fullTriangleStationaryOffset at *
  linarith only [mul_nonneg hd hgain,
    mul_nonneg (sq_nonneg d) (show 0 ≤ 32 / 9 + 2 * (1 - k) * (w + 1) by positivity)]

-- Increasing the diagonal offset raises the linear area reward faster than
-- the stationary square can grow. Increasing floor depths only helps.
theorem triangleCornerScore_mono_offset {a h k K c bR bL w : ℝ}
    (hk : k ≤ K) (hK : K ≤ 1)
    (ha : 1 ≤ a) (hh : 0 ≤ h) (hh1 : h ≤ 1 / 3)
    (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hz : fullTriangleStationaryOffset a K c - (1 - K) * h / 4 ≤ 3 / 4)
    (hR0 : 0 ≤ bR - (2 * c - (1 + k)))
    (hL0 : 0 ≤ bL - (2 * c - (1 + k)))
    (hR1 : bR - (2 * c - (1 + k)) ≤ 1 / 4)
    (hL1 : bL - (2 * c - (1 + k)) ≤ 1 / 4) :
    triangleCornerScore a h k c bR bL w ≤ triangleCornerScore a h K c bR bL w := by
  set d := K - k
  set z := fullTriangleStationaryOffset a K c - (1 - K) * h / 4
  set p := bR - (2 * c - (1 + k))
  set q := bL - (2 * c - (1 + k))
  set m := 3 * a / 2 + h / 4
  have hd : 0 ≤ d := sub_nonneg.2 hk
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hA : 0 ≤ 1 - K := by linarith
  have hp2 : p ^ 2 ≤ 1 / 16 := by nlinarith
  have hq2 : q ^ 2 ≤ 1 / 16 := by nlinarith
  have hf : w * p ^ 2 + q ^ 2 ≤ 1 / 8 := by nlinarith [mul_le_mul_of_nonneg_left hp2 hw]
  have hz' : z ≤ 3 / 4 := hz
  have hg : 0 ≤ a + 1 - h / 2 - 4 * m * z / 9 - (w * p ^ 2 + q ^ 2) / 2 := by
    dsimp [m] at *
    nlinarith [mul_le_mul_of_nonneg_left hz' hm]
  have hfloor : 0 ≤ (1 - K) * (w * (2 * p + d) + (2 * q + d)) := by
    positivity
  unfold triangleCornerScore
  dsimp [d, z, p, q, m] at *
  unfold fullTriangleStationaryOffset at *
  linarith only [mul_nonneg hd hg, mul_nonneg (hd) hfloor,
    sq_nonneg ((K - k) * (3 * a / 2 + h / 4))]

theorem triangle_stationary_offset_bounds {a k c : ℝ}
    (ha0 : 73 / 50 ≤ a) (ha1 : a ≤ 37 / 25)
    (hk0 : diagonalOffsetLower < k) (hk1 : k < 29 / 70)
    (hc0 : 12 / 13 < c) (hc1 : c < 73 / 79) :
    2 / 3 < fullTriangleStationaryOffset a k c ∧
      fullTriangleStationaryOffset a k c < 71 / 100 := by
  have hk : 0 ≤ 2 + 3 * k := by
    norm_num [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at hk0
    linarith
  have hlo := mul_le_mul_of_nonneg_left ha0 hk
  have hhi := mul_le_mul_of_nonneg_left ha1 hk
  unfold fullTriangleStationaryOffset
  norm_num [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at hk0
  constructor <;> linarith only [hlo, hhi, hk0, hk1, hc0, hc1]

/-- Enclose `cos(π/8)` by Newton steps for its reciprocal norm. -/
abbrev triangleCosUpper : ℝ :=
  let Q := 2 - 2 * diagonalOffsetUpper
  squareRootNewton Q (squareRootNewton Q 1) / Q

theorem triangle_parameter_bounds {k c : ℝ} (hk : 0 < k)
    (hksq : k ^ 2 + 2 * k = 1) (hc : 0 < c) (hcsq : c ^ 2 * (2 - 2 * k) = 1) :
    diagonalOffsetLower < k ∧ k < 29 / 70 ∧ 12 / 13 < c ∧ c < 73 / 79 ∧
      k ≤ diagonalOffsetUpper ∧ c ≤ triangleCosUpper := by
  have hK0 : (0 : ℝ) < diagonalOffsetUpper := by
    norm_num [diagonalOffsetUpper, squareRootNewton]
  have hK : diagonalOffsetUpper ^ 2 + 2 * diagonalOffsetUpper > (1 : ℝ) := by
    norm_num [diagonalOffsetUpper, squareRootNewton]
  have hL : diagonalOffsetLower ^ 2 + 2 * diagonalOffsetLower < (1 : ℝ) := by
    norm_num [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton]
  have hLo : (0 : ℝ) < diagonalOffsetLower := by
    norm_num [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton]
  have hKN : k ≤ diagonalOffsetUpper := by
    by_contra! h
    linarith only [hksq, hK, mul_pos (sub_pos.2 h) (by linarith : 0 < k + diagonalOffsetUpper + 2)]
  have hk0 : diagonalOffsetLower < k := by
    by_contra! h
    linarith only [hksq, hL, mul_nonneg (sub_nonneg.2 h) (by linarith : 0 ≤ diagonalOffsetLower + k + 2)]
  have hk1 : k < 29 / 70 := hKN.trans_lt (by norm_num [diagonalOffsetUpper, squareRootNewton])
  have hc0 : 12 / 13 < c := by
    have hcorner : (12 / 13 : ℝ) ^ 2 * (2 - 2 * diagonalOffsetLower) < 1 := by
      norm_num [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton]
    have hkpos : 0 < 2 - 2 * k := by nlinarith [sq_nonneg k]
    by_contra! h
    have hs : c ^ 2 ≤ (12 / 13 : ℝ) ^ 2 := by nlinarith
    have hprod := mul_le_mul_of_nonneg_right hs hkpos.le
    have hprod' := mul_lt_mul_of_pos_left (show 2 - 2 * k < 2 - 2 * diagonalOffsetLower by linarith) (by norm_num : (0 : ℝ) < (12 / 13) ^ 2)
    linarith only [hcsq, hprod, hprod', hcorner]
  have hc1 : c < 73 / 79 := by
    have hcorner : (73 / 79 : ℝ) ^ 2 * (2 - 2 * (29 / 70)) > 1 := by norm_num
    by_contra! h
    have hs : (73 / 79 : ℝ) ^ 2 ≤ c ^ 2 := by nlinarith
    have hprod := mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 - 2 * (29 / 70))
    have hprod' := mul_lt_mul_of_pos_left (show 2 - 2 * (29 / 70) < 2 - 2 * k by linarith) (sq_pos_of_pos hc)
    linarith only [hcsq, hprod, hprod', hcorner]
  have hcN : c ≤ triangleCosUpper := by
    have hQ : (0 : ℝ) < 2 - 2 * diagonalOffsetUpper := by norm_num [diagonalOffsetUpper, squareRootNewton]
    have hcorner : triangleCosUpper ^ 2 * (2 - 2 * diagonalOffsetUpper) ≥ (1 : ℝ) := by
      norm_num [triangleCosUpper, diagonalOffsetUpper, squareRootNewton]
    have hCN : (0 : ℝ) < triangleCosUpper := by norm_num [triangleCosUpper, diagonalOffsetUpper, squareRootNewton]
    have hcr := mul_le_mul_of_nonneg_left (show 2 - 2 * diagonalOffsetUpper ≤ 2 - 2 * k by linarith) (sq_nonneg c)
    by_contra! h
    have hs : triangleCosUpper ^ 2 < c ^ 2 := by nlinarith
    have hprod := mul_lt_mul_of_pos_right hs hQ
    linarith only [hcr, hcsq, hcorner, hprod]
  exact ⟨hk0, hk1, hc0, hc1, hKN, hcN⟩

/-- One comparison rectangle covers the three minimum-height corner checks. -/
theorem triangleCornerScore_le_Newton {a h k c bR bL w : ℝ}
    (hk : 0 < k) (hksq : k ^ 2 + 2 * k = 1)
    (hc : 0 < c) (hcsq : c ^ 2 * (2 - 2 * k) = 1)
    (ha : 73 / 50 ≤ a) (ha1 : a ≤ 37 / 25) (hh : 0 ≤ h) (hh1 : h ≤ 1 / 3)
    (hR0 : 1 / 2 - 1 / 80 ≤ bR) (hR1 : bR ≤ 2 / 3)
    (hL0 : 1 / 2 - 1 / 80 ≤ bL) (hL1 : bL ≤ 2 / 3)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    triangleCornerScore a h k c bR bL w ≤
      triangleCornerScore a h diagonalOffsetUpper triangleCosUpper bR bL w := by
  obtain ⟨hk0, hk1, hc0, hc1, hKN, hcN⟩ := triangle_parameter_bounds hk hksq hc hcsq
  have hK0 : (0 : ℝ) < diagonalOffsetUpper := by norm_num [diagonalOffsetUpper, squareRootNewton]
  have hC0 : (12 / 13 : ℝ) < triangleCosUpper := by norm_num [triangleCosUpper, diagonalOffsetUpper, squareRootNewton]
  have hC1 : triangleCosUpper < (73 / 79 : ℝ) := by norm_num [triangleCosUpper, diagonalOffsetUpper, squareRootNewton]
  have hN := mul_le_mul_of_nonneg_right (show 1 - k ≤ 3 / 5 by
    norm_num [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at hk0; linarith) hh
  have hz0 : 3 / 5 ≤ fullTriangleStationaryOffset a k triangleCosUpper - (1 - k) * h / 4 := by
    unfold fullTriangleStationaryOffset
    have hmul := mul_le_mul_of_nonneg_left ha (show 0 ≤ 2 + 3 * k by positivity)
    norm_num [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at hk0
    linarith
  have hz1 : fullTriangleStationaryOffset a diagonalOffsetUpper triangleCosUpper -
      (1 - diagonalOffsetUpper) * h / 4 ≤ 3 / 4 := by
    unfold fullTriangleStationaryOffset
    have hmul := mul_le_mul_of_nonneg_left ha1 (show 0 ≤ 2 + 3 * diagonalOffsetUpper by positivity)
    have hnonneg := mul_nonneg (show 0 ≤ 1 - diagonalOffsetUpper by norm_num [diagonalOffsetUpper, squareRootNewton]) hh
    norm_num [diagonalOffsetUpper, squareRootNewton] at *
    linarith
  have ht : 2 / 5 ≤ k := by
    norm_num [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at hk0; linarith
  have hR : bR - (2 * c - (1 + k)) ≤ 1 / 4 := by linarith
  have hL : bL - (2 * c - (1 + k)) ≤ 1 / 4 := by linarith
  apply (triangleCornerScore_mono_cos hcN ht (by linarith) hw hw1 hz0 hR hL).trans
  apply triangleCornerScore_mono_offset hKN (by norm_num [diagonalOffsetUpper, squareRootNewton])
    (by linarith) hh hh1 hw hw1 hz1
  · norm_num [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at hk0
    linarith
  · norm_num [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at hk0
    linarith
  · linarith
  · linarith

/-- Tilt payment and one generated corner check bound the complete full-floor correction. -/
theorem fullTriangleRelaxation_add_loss_lt {a h k c u v : ℝ}
    (ha : 37 / 25 ≤ a) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 3)
    (hk : 0 < k) (hksq : k ^ 2 + 2 * k = 1)
    (hc : 0 < c) (hcsq : c ^ 2 * (2 - 2 * k) = 1)
    (hq : 0 ≤ (u + v - h) / 2 - k) :
    fullTriangleRelaxation a h k c u v + fullTriangleLoss h k c < referenceHalfAreaLower := by
  obtain ⟨hk0, hk1, hc0, hc1, -, -⟩ := triangle_parameter_bounds hk hksq hc hcsq
  obtain ⟨hs0, hs1⟩ := triangle_stationary_offset_bounds (by norm_num : (73 / 50 : ℝ) ≤ 37 / 25)
    le_rfl hk0 hk1 hc0 hc1
  have hbound := fullTriangleRelaxation_le_bound ha (by norm_num) hh0 hh1 hk0 hk1 hksq hs0 hs1 hq
  have ht : 2 / 5 ≤ k := by
    norm_num [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at hk0; linarith
  have hheight : fullTriangleBound (37 / 25) h k c + fullTriangleLoss h k c ≤
      triangleCornerScore (37 / 25) 0 k c (3 / 5) (3 / 5) 1 := by
    have hpay := triangle_tilt_payment (s := fullTriangleStationaryOffset (37 / 25) k c)
      (p := 3 / 5 - (2 * c - (1 + k))) (q := 3 / 5 - (2 * c - (1 + k)))
      (r := -1 / 4) (t := 3 / 4) (h0 := 0) (h := h) ht (by linarith)
      (by linarith) (by linarith) (by norm_num) hh0 (by norm_num) (by linarith)
    unfold fullTriangleBound fullTriangleLoss triangleCornerScore
    linarith only [hpay, hksq]
  have hcorner := triangleCornerScore_le_Newton (a := 37 / 25) (h := 0)
    (bR := 3 / 5) (bL := 3 / 5) (w := 1) hk hksq hc hcsq
    (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hcheck : triangleCornerScore (37 / 25) 0 diagonalOffsetUpper triangleCosUpper (3 / 5) (3 / 5) 1 < referenceHalfAreaLower := by
    norm_num [triangleCornerScore, fullTriangleStationaryOffset, triangleCosUpper, diagonalOffsetUpper, squareRootNewton,
      referenceHalfAreaLower, referenceRootLower, cubicBracketLower, cubicBracketUpper, cubic]
  linarith only [hbound, hheight, hcorner, hcheck]

end AmbidextrousSofa
