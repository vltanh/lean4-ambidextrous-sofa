import AmbidextrousSofa.Analysis.FullTriangleScalar

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
  unfold fullTriangleStationaryOffset
  constructor <;> linarith only [hk0, hk1, hc0, hc1]

theorem tiltedTriangle_stationary_clip {k c h : ℝ}
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70)
    (hc0 : 923 / 1000 < c) (hc1 : c < 231 / 250)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 21 / 100) :
    let z := fullTriangleStationaryOffset (73 / 50) k c - (1 - k) * h / 4
    let M := (73 / 50 + k) / 2 + (2 - k) * z / 9 + h / 4
    0 < z ∧ 73 / 100 < M ∧ M < k + 73 / 100 ∧ 0 < M - h / 2 - k := by
  dsimp only
  let s0 := fullTriangleStationaryOffset (73 / 50) k c
  let z := s0 - (1 - k) * h / 4
  let M := (73 / 50 + k) / 2 + (2 - k) * z / 9 + h / 4
  obtain ⟨hs0, hs1⟩ := tiltedTriangle_stationary_offset_bounds hk0 hk1 hc0 hc1
  have hA : 0 < 1 - k ∧ 1 - k < 3 / 5 := by constructor <;> linarith only [hk0, hk1]
  have hb : 0 < 2 - k ∧ 2 - k < 8 / 5 := by constructor <;> linarith only [hk0, hk1]
  have hAh := mul_le_mul_of_nonneg_right hA.2.le hh0
  have hz : 0 < z := by dsimp [z, s0]; nlinarith only [hs0, hAh, hh1]
  have hM : 73 / 100 < M := by
    dsimp [M]
    nlinarith only [mul_pos hb.1 hz, hk0, hh0]
  have hBA : 3 / 4 < (2 - k) * (1 - k) := by
    nlinarith only [sq_nonneg k, hk1, hk0]
  have hsprod : (2 - k) * s0 < (8 / 5) * (7 / 10) := by
    have h := mul_lt_mul hb.2 hs1 (by linarith only [hs0] : 0 < s0) (by norm_num)
    exact h
  have hBAh := mul_le_mul_of_nonneg_right hBA.le hh0
  have hclip : M < k + 73 / 100 := by
    dsimp [M, z]
    nlinarith only [hk0, hsprod, hBAh, hh1]
  have hq : 0 < M - h / 2 - k := by
    dsimp [M]
    nlinarith only [mul_pos hb.1 hz, hk1, hh1]
  exact ⟨hz, hM, hclip, hq⟩

theorem tiltedTriangleRelaxation_le_bound {a h k c u v : ℝ}
    (ha : 73 / 50 ≤ a) (hh0 : 0 ≤ h) (hh1 : h ≤ 21 / 100)
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hc0 : 923 / 1000 < c) (hc1 : c < 231 / 250)
    (hq : 0 ≤ (u + v - h) / 2 - k) :
    fullTriangleRelaxation a h k c u v ≤ fullTriangleBound (73 / 50) h k c := by
  let a0 : ℝ := 73 / 50
  let b := 2 - k
  let d := 2 + 3 * k
  let z := fullTriangleStationaryOffset a0 k c - (1 - k) * h / 4
  let m := (a0 + k) / 2 + b * z / 9 + h / 4
  have hk : 0 < k := by linarith only [hk0]
  have hd : 0 < d := by dsimp [d]; linarith only [hk]
  have hb : 0 < b := by dsimp [b]; linarith only [hk1]
  have hBD : b ^ 2 + 2 * d = 9 := by dsimp [b, d]; nlinarith only [hksq]
  have hclip := tiltedTriangle_stationary_clip hk0 hk1 hc0 hc1 hh0 hh1
  change 0 < z ∧ 73 / 100 < m ∧ m < k + 73 / 100 ∧ 0 < m - h / 2 - k at hclip
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

/-- The asymmetric floor correction and the stationary value decrease
from height `1/20` throughout the entire remaining medium-tilt strip. -/
theorem tiltedTriangleBound_add_loss_lt {h k c : ℝ}
    (hh0 : 1 / 20 ≤ h) (hh1 : h ≤ 21 / 100)
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hc0 : 923 / 1000 < c) (hc1 : c < 231 / 250) :
    fullTriangleBound (73 / 50) h k c + tiltedTriangleLoss h k c <
      (7550393 / 9240000 : ℝ) := by
  let s0 := fullTriangleStationaryOffset (73 / 50) k c
  let A := 1 - k
  let γ := (1 - k) / 2
  let D := 1 / 2 - (2 * c - (1 + k))
  let ell := -k / 2 + A * s0 / 9 + γ * (D + 1 / 8)
  let q := -1 / 8 - A ^ 2 / 72 + 5 * γ / 8
  have hs := tiltedTriangle_stationary_offset_bounds hk0 hk1 hc0 hc1
  have hA : 0 < A ∧ A < 3 / 5 := by
    dsimp [A]
    constructor <;> linarith only [hk0, hk1]
  have hγ : 0 < γ ∧ γ < 3 / 10 := by
    dsimp [γ]
    constructor <;> linarith only [hk0, hk1]
  have hD : 21 / 400 < D ∧ D < 239 / 3500 := by
    dsimp [D]
    constructor <;> linarith only [hk0, hk1, hc0, hc1]
  have hAs : A * s0 < (3 / 5) * (7 / 10) :=
    mul_lt_mul hA.2 hs.2 (by linarith only [hs.1] : 0 < s0) (by norm_num)
  have hγD : γ * (D + 1 / 8) < (3 / 10) * (239 / 3500 + 1 / 8) :=
    mul_lt_mul hγ.2 (by linarith only [hD.2])
      (by linarith only [hD.1] : 0 < D + 1 / 8) (by norm_num)
  have hell : ell < -9 / 100 := by
    dsimp [ell]
    linarith only [hAs, hγD, hk0]
  have hq : q < 1 / 16 := by
    dsimp [q]
    linarith only [hγ.2, sq_nonneg A]
  have htilt : ell * (h - 1 / 20) + q * (h ^ 2 - (1 / 20 : ℝ) ^ 2) ≤ 0 := by
    have hδ : 0 ≤ h - 1 / 20 := sub_nonneg.mpr hh0
    have hsq : 0 ≤ h ^ 2 - (1 / 20 : ℝ) ^ 2 := by
      nlinarith only [mul_nonneg hδ (show 0 ≤ h + 1 / 20 by linarith only [hh0])]
    have h1 := mul_le_mul_of_nonneg_right hell.le hδ
    have h2 := mul_le_mul_of_nonneg_right hq.le hsq
    have h3 := mul_nonneg hδ (sub_nonneg.mpr hh1)
    nlinarith only [h1, h2, h3, hδ]
  have hexpand : fullTriangleBound (73 / 50) h k c + tiltedTriangleLoss h k c =
      fullTriangleBound (73 / 50) (1 / 20) k c + tiltedTriangleLoss (1 / 20) k c +
        ell * (h - 1 / 20) + q * (h ^ 2 - (1 / 20 : ℝ) ^ 2) := by
    dsimp [fullTriangleBound, tiltedTriangleLoss, s0, A, γ, D, ell, q]
    ring
  have hB : (73 / 50 : ℝ) - (73 / 50 - k) ^ 2 / 2 =
      (123 / 50) * k - 529 / 5000 := by
    nlinarith only [hksq]
  have hz : (53 / 80 : ℝ) < s0 - A / 80 := by
    dsimp [s0, A, fullTriangleStationaryOffset]
    linarith only [hk0, hc1]
  have hzsq : (53 / 80 : ℝ) ^ 2 < (s0 - A / 80) ^ 2 := by
    nlinarith only [mul_pos (sub_pos.mpr hz)
      (show 0 < s0 - A / 80 + 53 / 80 by linarith only [hz])]
  have hDR : 0 < D - 1 / 80 ∧ D - 1 / 80 < 7 / 125 := by
    constructor <;> linarith only [hD.1, hD.2]
  have hDL : 0 < D + 1 / 12 + 3 / 80 ∧ D + 1 / 12 + 3 / 80 < 19 / 100 := by
    constructor <;> linarith only [hD.1, hD.2]
  have hRsq : (D - 1 / 80) ^ 2 < (7 / 125 : ℝ) ^ 2 := by
    nlinarith only [mul_pos (sub_pos.mpr hDR.2)
      (show 0 < 7 / 125 + (D - 1 / 80) by linarith only [hDR.1])]
  have hLsq : (D + 1 / 12 + 3 / 80) ^ 2 < (19 / 100 : ℝ) ^ 2 := by
    nlinarith only [mul_pos (sub_pos.mpr hDL.2)
      (show 0 < 19 / 100 + (D + 1 / 12 + 3 / 80) by linarith only [hDL.1])]
  have hLoss : tiltedTriangleLoss (1 / 20) k c < 3 / 250 := by
    have hmul := mul_le_mul_of_nonneg_right hγ.2.le
      (add_nonneg (sq_nonneg (D - 1 / 80)) (sq_nonneg (D + 1 / 12 + 3 / 80)))
    have heq : tiltedTriangleLoss (1 / 20) k c =
        γ * ((D - 1 / 80) ^ 2 + (D + 1 / 12 + 3 / 80) ^ 2) := by
      dsimp [tiltedTriangleLoss, γ, D]
      ring
    rw [heq]
    nlinarith only [hmul, hRsq, hLsq]
  have hvalue : fullTriangleBound (73 / 50) (1 / 20) k c =
      (123 / 50) * k - 529 / 5000 - k / 40 - 1 / 3200 -
        (2 / 9) * (s0 - A / 80) ^ 2 := by
    unfold fullTriangleBound
    rw [hB]
    dsimp only [s0, A]
    ring
  rw [hexpand, hvalue]
  linarith only [htilt, hzsq, hLoss, hk0, hk1]

theorem tiltedTriangleRelaxation_add_loss_lt {a h k c u v : ℝ}
    (ha : 73 / 50 ≤ a) (hh0 : 1 / 20 ≤ h) (hh1 : h ≤ 21 / 100)
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hc0 : 923 / 1000 < c) (hc1 : c < 231 / 250)
    (hq : 0 ≤ (u + v - h) / 2 - k) :
    fullTriangleRelaxation a h k c u v + tiltedTriangleLoss h k c < (41 / 50 : ℝ) := by
  have hbound := tiltedTriangleRelaxation_le_bound ha (by linarith only [hh0]) hh1
    hk0 hk1 hksq hc0 hc1 hq
  have hstrict := tiltedTriangleBound_add_loss_lt hh0 hh1 hk0 hk1 hksq hc0 hc1
  linarith only [hbound, hstrict]

end AmbidextrousSofa
