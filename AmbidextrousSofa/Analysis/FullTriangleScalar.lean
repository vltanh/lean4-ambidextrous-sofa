import AmbidextrousSofa.Analysis.FullTriangleFloor
import AmbidextrousSofa.Analysis.IntermediateTilt

/-!
# Scalar payment and global supporting plane for three full triangles

Every clipping term is retained. At an unclipped comparison point the
two tail squares are bounded by their displacement squares; the remaining
quadratic form is nonpositive even when the width varies. A separate
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
  let r := 1 + k
  let x := max ZR 0
  let y := max ZL 0
  let N := x + y + (δR + δL) / 2
  let D := (δR ^ 2 + δL ^ 2) / (2 * k)
  let G := (x ^ 2 + y ^ 2) / r
  have hr : 0 < r := by dsimp [r]; linarith only [hk]
  have hN : 0 ≤ N := by dsimp [N, x, y]; positivity
  have hSN : max S 0 ≤ N := max_le
    (by dsimp [N, x, y]; linarith only [hS, le_max_left ZR 0, le_max_left ZL 0]) hN
  have hsq : (max S 0) ^ 2 ≤ N ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hSN)
      (add_nonneg hN (le_max_right S 0))]
  have hid : 2 * k * r * ((2 + 3 * k) * (D + G) - N ^ 2) =
      2 * k * r * (x - y) ^ 2 + (k * r / 2) * (δR - δL) ^ 2 +
      (k * x - r * δR) ^ 2 + (k * x - r * δL) ^ 2 +
      (k * y - r * δR) ^ 2 + (k * y - r * δL) ^ 2 := by
    dsimp [D, G, N, r]
    field_simp [hk.ne', (by linarith only [hk] : 1 + k ≠ 0)] <;> ring
  have hnonneg : 0 ≤ 2 * k * r * ((2 + 3 * k) * (D + G) - N ^ 2) := by
    rw [hid]
    positivity
  have hpay : N ^ 2 ≤ (2 + 3 * k) * (D + G) := by
    have h := (mul_nonneg_iff_of_pos_left (by positivity : 0 < 2 * k * r)).mp hnonneg
    linarith only [h]
  apply (div_le_iff₀ (by linarith only [hk] : 0 < 2 + 3 * k)).mpr
  change (max S 0) ^ 2 ≤ (D + G) * (2 + 3 * k)
  nlinarith only [hsq, hpay]

/-- The complete diagonal relaxation has a global supporting plane in
width and both diagonal supports at an inactive-tail comparison point. -/
theorem diagonalRelaxation_le_joint_tangent (h k : ℝ) {a u v a0 u0 v0 : ℝ}
    (hq : 0 ≤ (u + v - h) / 2 - k)
    (hq0 : 0 ≤ (u0 + v0 - h) / 2 - k)
    (hu0 : u0 ≤ k + a0 / 2) (hv0 : v0 ≤ h + k + a0 / 2) :
    diagonalRelaxation a h k u v ≤
      a0 - ((a0 - u0) ^ 2 + (a0 - v0) ^ 2) / 2 - a0 * h / 2 -
        ((u0 + v0 - h) / 2 - k) ^ 2 +
      (1 - h / 2 - (2 * a0 - u0 - v0)) * (a - a0) +
      (a0 - u0 - ((u0 + v0 - h) / 2 - k)) * (u - u0) +
      (a0 - v0 - ((u0 + v0 - h) / 2 - k)) * (v - v0) := by
  have hclipR := shifted_positive_square_le_displacement (u - a / 2)
    (show u0 - a0 / 2 ≤ k by linarith only [hu0])
  have hclipL := shifted_positive_square_le_displacement (v - a / 2)
    (show v0 - a0 / 2 ≤ h + k by linarith only [hv0])
  rw [show u - a / 2 - k = u - k - a / 2 by ring] at hclipR
  rw [show v - a / 2 - (h + k) = v - h - k - a / 2 by ring] at hclipL
  unfold diagonalRelaxation
  rw [max_eq_left hq]
  nlinarith only [hclipR, hclipL, sq_nonneg (a - a0),
    sq_nonneg ((u - u0 + (v - v0)) / 2 - (a - a0) / 2)]

theorem fullTriangleRelaxation_le_joint_tangent {a h k c u v a0 u0 v0 : ℝ}
    (hk : 0 < k)
    (hq : 0 ≤ (u + v - h) / 2 - k)
    (hq0 : 0 ≤ (u0 + v0 - h) / 2 - k)
    (hu0 : u0 ≤ k + a0 / 2) (hv0 : v0 ≤ h + k + a0 / 2)
    (hS0 : 0 ≤ fullTriangleDemand a0 ((u0 + v0) / 2) h k c) :
    let S0 := fullTriangleDemand a0 ((u0 + v0) / 2) h k c
    fullTriangleRelaxation a h k c u v ≤
      a0 - ((a0 - u0) ^ 2 + (a0 - v0) ^ 2) / 2 - a0 * h / 2 -
        ((u0 + v0 - h) / 2 - k) ^ 2 - S0 ^ 2 / (2 + 3 * k) +
      (1 - h / 2 - (2 * a0 - u0 - v0) - 2 * S0 * (k + 2) / (2 + 3 * k)) * (a - a0) +
      (a0 - u0 - ((u0 + v0 - h) / 2 - k) - S0 * (k - 2) / (2 + 3 * k)) * (u - u0) +
      (a0 - v0 - ((u0 + v0 - h) / 2 - k) - S0 * (k - 2) / (2 + 3 * k)) * (v - v0) := by
  dsimp only
  have hF := diagonalRelaxation_le_joint_tangent h k hq hq0 hu0 hv0
  have hS := positive_square_ge_tangent
    (fullTriangleDemand a ((u + v) / 2) h k c) hS0
  have hden : 0 < 2 + 3 * k := by linarith only [hk]
  have hscale := div_le_div_of_nonneg_right hS hden.le
  have hdiff : fullTriangleDemand a ((u + v) / 2) h k c -
      fullTriangleDemand a0 ((u0 + v0) / 2) h k c =
        (k + 2) * (a - a0) + ((k - 2) / 2) * ((u - u0) + (v - v0)) := by
    unfold fullTriangleDemand
    ring
  rw [hdiff] at hscale
  have hscale' :
      (fullTriangleDemand a0 ((u0 + v0) / 2) h k c) ^ 2 / (2 + 3 * k) +
      (2 * fullTriangleDemand a0 ((u0 + v0) / 2) h k c * (k + 2) / (2 + 3 * k)) * (a - a0) +
      (fullTriangleDemand a0 ((u0 + v0) / 2) h k c * (k - 2) / (2 + 3 * k)) * (u - u0) +
      (fullTriangleDemand a0 ((u0 + v0) / 2) h k c * (k - 2) / (2 + 3 * k)) * (v - v0) ≤
        (max (fullTriangleDemand a ((u + v) / 2) h k c) 0) ^ 2 / (2 + 3 * k) := by
    convert hscale using 1 <;> ring
  unfold fullTriangleRelaxation
  nlinarith only [hF, hscale']

theorem fullTriangle_stationary_offset_bounds {k c : ℝ}
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70)
    (hc0 : 923 / 1000 < c) (hc1 : c < 231 / 250) :
    703 / 1000 < fullTriangleStationaryOffset (37 / 25) k c ∧
      fullTriangleStationaryOffset (37 / 25) k c < 71 / 100 := by
  unfold fullTriangleStationaryOffset
  constructor <;> linarith only [hk0, hk1, hc0, hc1]

theorem fullTriangle_stationary_clip {k c h : ℝ}
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70)
    (hc0 : 923 / 1000 < c) (hc1 : c < 231 / 250)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 17 / 50) :
    let z := fullTriangleStationaryOffset (37 / 25) k c - (1 - k) * h / 4
    let M := (37 / 25 + k) / 2 + (2 - k) * z / 9 + h / 4
    0 < z ∧ 37 / 50 < M ∧ M < k + 37 / 50 ∧ 0 < M - h / 2 - k := by
  dsimp only
  let s0 := fullTriangleStationaryOffset (37 / 25) k c
  let z := s0 - (1 - k) * h / 4
  let M := (37 / 25 + k) / 2 + (2 - k) * z / 9 + h / 4
  obtain ⟨hs0, hs1⟩ := fullTriangle_stationary_offset_bounds hk0 hk1 hc0 hc1
  have hA : 0 < 1 - k ∧ 1 - k < 3 / 5 := by constructor <;> linarith only [hk0, hk1]
  have hb : 0 < 2 - k ∧ 2 - k < 8 / 5 := by constructor <;> linarith only [hk0, hk1]
  have hAh := mul_le_mul_of_nonneg_right hA.2.le hh0
  have hz : 0 < z := by dsimp [z, s0]; nlinarith only [hs0, hAh, hh1]
  have hM : 37 / 50 < M := by
    dsimp [M]
    nlinarith only [mul_pos hb.1 hz, hk0, hh0]
  have hBA : 3 / 4 < (2 - k) * (1 - k) := by
    nlinarith only [sq_nonneg k, hk1, hk0]
  have hsprod : (2 - k) * s0 < (8 / 5) * (71 / 100) := by
    have h := mul_lt_mul hb.2 hs1 (by linarith only [hs0] : 0 < s0) (by norm_num)
    exact h
  have hBAh := mul_le_mul_of_nonneg_right hBA.le hh0
  have hclip : M < k + 37 / 50 := by
    dsimp [M, z]
    nlinarith only [hk0, hsprod, hBAh, hh1]
  have hq : 0 < M - h / 2 - k := by
    dsimp [M]
    nlinarith only [mul_pos hb.1 hz, hk1, hh1]
  exact ⟨hz, hM, hclip, hq⟩

theorem fullTriangleRelaxation_le_bound {a h k c u v : ℝ}
    (ha : 37 / 25 ≤ a) (hh0 : 0 ≤ h) (hh1 : h ≤ 17 / 50)
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hc0 : 923 / 1000 < c) (hc1 : c < 231 / 250)
    (hq : 0 ≤ (u + v - h) / 2 - k) :
    fullTriangleRelaxation a h k c u v ≤ fullTriangleBound (37 / 25) h k c := by
  let a0 : ℝ := 37 / 25
  let b := 2 - k
  let d := 2 + 3 * k
  let z := fullTriangleStationaryOffset a0 k c - (1 - k) * h / 4
  let m := (a0 + k) / 2 + b * z / 9 + h / 4
  have hk : 0 < k := by linarith only [hk0]
  have hd : 0 < d := by dsimp [d]; linarith only [hk]
  have hb : 0 < b := by dsimp [b]; linarith only [hk1]
  have hBD : b ^ 2 + 2 * d = 9 := by dsimp [b, d]; nlinarith only [hksq]
  have hclip := fullTriangle_stationary_clip hk0 hk1 hc0 hc1 hh0 hh1
  change 0 < z ∧ 37 / 50 < m ∧ m < k + 37 / 50 ∧ 0 < m - h / 2 - k at hclip
  have hS : fullTriangleDemand a0 m h k c = 2 * d * z / 9 := by
    have heq : fullTriangleDemand a0 m h k c =
        z - b ^ 2 * z / 9 + (k ^ 2 + 2 * k - 1) / 2 := by
      dsimp [fullTriangleDemand, m, z, b, d, fullTriangleStationaryOffset]
      ring
    rw [heq, hksq]
    have h := congrArg (fun w : ℝ => w * z) hBD
    nlinarith only [h]
  have hgrad : a0 - m - (m - h / 2 - k) - (2 * d * z / 9) * (k - 2) / d = 0 := by
    dsimp [m, b]
    field_simp [hd.ne'] <;> ring
  have hgradA : 1 - h / 2 - (2 * a0 - m - m) -
      2 * (2 * d * z / 9) * (k + 2) / d = 1 + k - a0 - 2 * d * z / 9 := by
    dsimp [m, b, d]
    field_simp [(by dsimp [d] at hd; exact hd.ne' : 2 + 3 * k ≠ 0)] <;> ring
  have hvalue : a0 - ((a0 - m) ^ 2 + (a0 - m) ^ 2) / 2 - a0 * h / 2 -
      (m - h / 2 - k) ^ 2 - (2 * d * z / 9) ^ 2 / d =
        fullTriangleBound a0 h k c := by
    calc
      _ = a0 - (a0 - k) ^ 2 / 2 - k * h / 2 - h ^ 2 / 8 -
          (2 / 81) * (b ^ 2 + 2 * d) * z ^ 2 := by
        dsimp [m]
        field_simp [hd.ne'] <;> ring
      _ = _ := by rw [hBD]; dsimp [fullTriangleBound, z]; ring
  have hmMean : (m + m) / 2 = m := by ring
  have hmQ : (m + m - h) / 2 - k = m - h / 2 - k := by ring
  have htan := fullTriangleRelaxation_le_joint_tangent (a0 := a0) (u0 := m) (v0 := m)
    hk hq (by rw [hmQ]; exact hclip.2.2.2.le) hclip.2.2.1.le
    (by dsimp [a0]; linarith only [hclip.2.2.1, hh0])
    (by rw [hmMean, hS]; positivity)
  dsimp only at htan
  rw [hmMean, hmQ, hS] at htan
  change fullTriangleRelaxation a h k c u v ≤
    a0 - ((a0 - m) ^ 2 + (a0 - m) ^ 2) / 2 - a0 * h / 2 -
      (m - h / 2 - k) ^ 2 - (2 * d * z / 9) ^ 2 / d +
    (1 - h / 2 - (2 * a0 - m - m) - 2 * (2 * d * z / 9) * (k + 2) / d) * (a - a0) +
    (a0 - m - (m - h / 2 - k) - (2 * d * z / 9) * (k - 2) / d) * (u - m) +
    (a0 - m - (m - h / 2 - k) - (2 * d * z / 9) * (k - 2) / d) * (v - m) at htan
  rw [hvalue, hgradA, hgrad, zero_mul, add_zero, add_zero] at htan
  have hneg : 1 + k - a0 - 2 * d * z / 9 ≤ 0 := by
    dsimp [a0]
    nlinarith only [hk1, mul_pos hd hclip.1]
  have hprod := mul_nonpos_of_nonpos_of_nonneg hneg (sub_nonneg.mpr ha)
  exact htan.trans (by linarith only [hprod])

/-- The supporting-plane value plus the entire floor loss decreases
over the allowed tilt interval. The final separation is rational. -/
theorem fullTriangleBound_add_loss_lt {h k c : ℝ}
    (hh0 : 0 ≤ h) (hh1 : h ≤ 17 / 50)
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hc0 : 923 / 1000 < c) (hc1 : c < 231 / 250) :
    fullTriangleBound (37 / 25) h k c + fullTriangleLoss h k c <
      (25811237 / 31500000 : ℝ) := by
  let s0 := fullTriangleStationaryOffset (37 / 25) k c
  let A := 1 - k
  let γ := (1 - k) / 2
  let d0 := 3 / 5 - (2 * c - (1 + k))
  let ell := -k / 2 + A * s0 / 9 + γ * d0
  let q := -1 / 8 - A ^ 2 / 72 + 5 * γ / 8
  have hs := fullTriangle_stationary_offset_bounds hk0 hk1 hc0 hc1
  have hA : 0 < A ∧ A < 3 / 5 := by dsimp [A]; constructor <;> linarith only [hk0, hk1]
  have hγ : 0 < γ ∧ γ < 3 / 10 := by dsimp [γ]; constructor <;> linarith only [hk0, hk1]
  have hd : 0 < d0 ∧ d0 < 589 / 3500 := by
    dsimp [d0]
    constructor <;> linarith only [hc0, hc1, hk0, hk1]
  have hAs : A * s0 < (3 / 5) * (71 / 100) :=
    mul_lt_mul hA.2 hs.2 (by linarith only [hs.1] : 0 < s0) (by norm_num)
  have hγd : γ * d0 < (3 / 10) * (589 / 3500) :=
    mul_lt_mul hγ.2 hd.2 hd.1 (by norm_num)
  have hell : ell < -1 / 10 := by dsimp [ell]; linarith only [hAs, hγd, hk0]
  have hq : q < 1 / 16 := by dsimp [q]; linarith only [hγ.2, sq_nonneg A]
  have htilt : ell * h + q * h ^ 2 ≤ 0 := by
    have h1 := mul_le_mul_of_nonneg_right hell.le hh0
    have h2 := mul_le_mul_of_nonneg_right hq.le (sq_nonneg h)
    have h3 := mul_nonneg hh0 (sub_nonneg.mpr hh1)
    nlinarith only [h1, h2, h3, hh0]
  have hexpand : fullTriangleBound (37 / 25) h k c + fullTriangleLoss h k c =
      (37 / 25 - (37 / 25 - k) ^ 2 / 2 - (2 / 9) * s0 ^ 2 + 2 * γ * d0 ^ 2) +
        ell * h + q * h ^ 2 := by
    dsimp [fullTriangleBound, fullTriangleLoss, s0, A, γ, d0, ell, q]
    ring
  have hB : (37 / 25 : ℝ) - (37 / 25 - k) ^ 2 / 2 = (62 / 25) * k - 72 / 625 := by
    nlinarith only [hksq]
  have hs2 : (703 / 1000 : ℝ) ^ 2 < s0 ^ 2 := by
    nlinarith only [mul_pos (sub_pos.mpr hs.1)
      (show 0 < s0 + 703 / 1000 by linarith only [hs.1])]
  have hd2 : d0 ^ 2 < (589 / 3500 : ℝ) ^ 2 := by
    nlinarith only [mul_pos (sub_pos.mpr hd.2)
      (show 0 < 589 / 3500 + d0 by linarith only [hd.1])]
  have hγd2 : 2 * γ * d0 ^ 2 < 17 / 1000 := by
    have hm := mul_le_mul_of_nonneg_right hγ.2.le (sq_nonneg d0)
    nlinarith only [hm, hd2]
  rw [hexpand, hB]
  linarith only [htilt, hs2, hγd2, hk1]

theorem fullTriangleRelaxation_add_loss_lt {a h k c u v : ℝ}
    (ha : 37 / 25 ≤ a) (hh0 : 0 ≤ h) (hh1 : h ≤ 17 / 50)
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hc0 : 923 / 1000 < c) (hc1 : c < 231 / 250)
    (hq : 0 ≤ (u + v - h) / 2 - k) :
    fullTriangleRelaxation a h k c u v + fullTriangleLoss h k c < (41 / 50 : ℝ) := by
  have hbound := fullTriangleRelaxation_le_bound ha hh0 hh1 hk0 hk1 hksq hc0 hc1 hq
  have hstrict := fullTriangleBound_add_loss_lt hh0 hh1 hk0 hk1 hksq hc0 hc1
  linarith only [hbound, hstrict]

end AmbidextrousSofa
