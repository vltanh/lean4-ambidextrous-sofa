module

public import AmbidextrousSofa.Analysis.NearDiagonalWalls

@[expose] public section

/-!
# Exact constants for the short-width two-tail payment

All numerical margins are rational consequences of `k²+2k=1` and the
displayed rational bounds for k. The final paid envelope decreases with
nonnegative tilt and lies strictly below 41/50, including widths up to
1001/1000 in the half-projection parameter.
-/

noncomputable section

namespace AmbidextrousSofa

def nearTriangleCoefficient (k : ℝ) : ℝ := 1 / (2 * k * (1 - k))

def shortOuterTipAllowance (k : ℝ) : ℝ := 323 / 1000 - k + (2 / 25) / k

def shortWidthPaidEnvelope (k h : ℝ) : ℝ :=
  (2001 / 1000) * k - 1 / 2000000 - k * h / 2 - h ^ 2 / 8 -
    nearTriangleCoefficient k / 2 * (((2 / 25) - (1 - k) * h) ^ 2 + (2 / 25) ^ 2) +
      k * (shortOuterTipAllowance k + h / 4) ^ 2

theorem diagonal_offset_inv {k : ℝ} (hk : 0 < k) (hksq : k ^ 2 + 2 * k = 1) :
    1 / k = k + 2 := by
  apply (div_eq_iff hk.ne').mpr
  nlinarith

theorem diagonal_complement_inv {k : ℝ} (hk1 : k < 1) (hksq : k ^ 2 + 2 * k = 1) :
    1 / (1 - k) = (3 + k) / 2 := by
  apply (div_eq_iff (sub_pos.mpr hk1).ne').mpr
  nlinarith

theorem nearTriangleCoefficient_eq {k : ℝ} (hk : 0 < k) (hk1 : k < 1)
    (hksq : k ^ 2 + 2 * k = 1) : nearTriangleCoefficient k = (7 + 3 * k) / 4 := by
  unfold nearTriangleCoefficient
  apply (div_eq_iff (by positivity : 2 * k * (1 - k) ≠ 0)).mpr
  linear_combination (3 * k / 2 - 1) * hksq

theorem nearTriangleCoefficient_mul_complement {k : ℝ} (hk : 0 < k) (hk1 : k < 1)
    (hksq : k ^ 2 + 2 * k = 1) : nearTriangleCoefficient k * (1 - k) = (k + 2) / 2 := by
  calc
    _ = (1 / k) / 2 := by
      unfold nearTriangleCoefficient
      field_simp [hk.ne', (sub_pos.mpr hk1).ne'] <;> ring
    _ = _ := by rw [diagonal_offset_inv hk hksq]

theorem shortOuterTipAllowance_eq {k : ℝ} (hk : 0 < k) (hksq : k ^ 2 + 2 * k = 1) :
    shortOuterTipAllowance k = (483 - 920 * k) / 1000 := by
  have hinv := diagonal_offset_inv hk hksq
  have hdiv : (2 / 25 : ℝ) / k = (2 / 25) * (1 / k) := by ring
  unfold shortOuterTipAllowance
  rw [hdiv, hinv]
  ring

theorem short_nearDiagonal_constants {k : ℝ}
    (hk0 : 2 / 5 < k) (hk1 : k < 169 / 408) (hksq : k ^ 2 + 2 * k = 1) :
    (2 / 25 : ℝ) < 1 - nearDiagonalNorm k + k ^ 2 ∧
      nearDiagonalNorm k + (2 / 25) / k < 32 / 25 ∧
      k + (2 / 25) / (1 - k) < 3 / 5 ∧
      0 < shortOuterTipAllowance k := by
  have hk : 0 < k := by linarith
  have hklt : k < 1 := by linarith
  have hb := nearDiagonalNorm_pos k
  have hbsq := nearDiagonalNorm_sq k
  have hk7 : 7 / 17 < k := by
    by_contra hbad
    have hprod := mul_nonneg (show 0 ≤ 7 / 17 - k by linarith [le_of_not_gt hbad])
      (show 0 ≤ 7 / 17 + k by linarith)
    nlinarith
  have hbfirst : nearDiagonalNorm k < 48 / 25 - 2 * k := by
    by_contra hbad
    have hprod := mul_nonneg
      (show 0 ≤ nearDiagonalNorm k - (48 / 25 - 2 * k) by linarith [le_of_not_gt hbad])
      (show 0 ≤ nearDiagonalNorm k + (48 / 25 - 2 * k) by linarith)
    nlinarith
  have hbsecond : nearDiagonalNorm k < (28 - 2 * k) / 25 := by
    by_contra hbad
    have hprod := mul_nonneg
      (show 0 ≤ nearDiagonalNorm k - (28 - 2 * k) / 25 by linarith [le_of_not_gt hbad])
      (show 0 ≤ nearDiagonalNorm k + (28 - 2 * k) / 25 by linarith)
    nlinarith
  have hdiv : (2 / 25 : ℝ) / k = (2 / 25) * (k + 2) := by
    calc
      _ = (2 / 25) * (1 / k) := by ring
      _ = _ := by rw [diagonal_offset_inv hk hksq]
  have hdivc : (2 / 25 : ℝ) / (1 - k) = (2 / 25) * ((3 + k) / 2) := by
    calc
      _ = (2 / 25) * (1 / (1 - k)) := by ring
      _ = _ := by rw [diagonal_complement_inv hklt hksq]
  refine ⟨by nlinarith, ?_, ?_, ?_⟩
  · rw [hdiv]
    linarith
  · rw [hdivc]
    linarith
  · rw [shortOuterTipAllowance_eq hk hksq]
    linarith

theorem shortWidthPaidEnvelope_lt {k h : ℝ}
    (hk0 : 2 / 5 < k) (hk1 : k < 169 / 408) (hksq : k ^ 2 + 2 * k = 1)
    (hh : 0 ≤ h) : shortWidthPaidEnvelope k h < (41 / 50 : ℝ) := by
  have hk : 0 < k := by linarith
  have hklt : k < 1 := by linarith
  let G := nearTriangleCoefficient k
  let L := shortOuterTipAllowance k
  let H0 := (2001 / 1000) * k - 1 / 2000000 - G * (2 / 25) ^ 2 + k * L ^ 2
  let linear := -k / 2 + G * (2 / 25) * (1 - k) + k * L / 2
  let quadratic := -1 / 8 - G * (1 - k) ^ 2 / 2 + k / 16
  have hG : G = (7 + 3 * k) / 4 := nearTriangleCoefficient_eq hk hklt hksq
  have hGc : G * (1 - k) = (k + 2) / 2 :=
    nearTriangleCoefficient_mul_complement hk hklt hksq
  have hL : L = (483 - 920 * k) / 1000 := shortOuterTipAllowance_eq hk hksq
  have hG0 : 0 ≤ G := by rw [hG]; linarith
  have hexpand : shortWidthPaidEnvelope k h = H0 + linear * h + quadratic * h ^ 2 := by
    dsimp [shortWidthPaidEnvelope, H0, linear, quadratic, G, L]
    ring
  have hlinear : linear = (1403 / 2000) * k - 19 / 50 := by
    dsimp [linear]
    rw [hL]
    nlinarith only [hGc, hksq]
  have hlinear0 : linear ≤ 0 := by rw [hlinear]; linarith
  have hquadratic0 : quadratic ≤ 0 := by
    have hprod := mul_nonneg hG0 (sq_nonneg (1 - k))
    dsimp [quadratic]
    linarith
  have hH : shortWidthPaidEnvelope k h ≤ H0 := by
    have hlin := mul_nonpos_of_nonpos_of_nonneg hlinear0 hh
    have hquad := mul_nonpos_of_nonpos_of_nonneg hquadratic0 (sq_nonneg h)
    rw [hexpand]
    linarith only [hlin, hquad]
  have hH0 : H0 = (8238929 / 1000000) * k - 5185441 / 2000000 := by
    have hcube := congrArg (fun z : ℝ => k * z) hksq
    dsimp [H0]
    rw [hG, hL]
    nlinarith only [hksq, hcube]
  apply hH.trans_lt
  rw [hH0]
  linarith

end AmbidextrousSofa
