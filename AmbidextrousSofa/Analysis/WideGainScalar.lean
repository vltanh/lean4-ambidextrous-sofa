import AmbidextrousSofa.Analysis.WideNichePieces

/-!
# Exact scalar payment for the two retained wide niche pieces

The truncation losses are bounded before the two positive heights are
combined with the exterior cuts. A rational quadratic inequality pays
the resulting positive square, and one global supporting plane excludes
the wide feasible region.
-/

noncomputable section

namespace AmbidextrousSofa

theorem wide_offset_inverse {k : ℝ} (hk : 0 < k) (hksq : k ^ 2 + 2 * k = 1) :
    1 / k = k + 2 := by
  apply (div_eq_iff hk.ne').mpr
  nlinarith only [hksq]

theorem wide_norm_rational_bounds {k : ℝ} (hk0 : 41 / 100 < k) (hk1 : k < 29 / 70) :
    27 / 25 < nearDiagonalNorm k ∧ nearDiagonalNorm k < 13 / 12 ∧
      3 / 2 < (1 + k) * nearDiagonalNorm k := by
  have hb := nearDiagonalNorm_pos k
  have hbsq := nearDiagonalNorm_sq k
  have hlo : 27 / 25 < nearDiagonalNorm k := by
    by_contra h
    have hp := mul_pos (show 0 < k - 41 / 100 by linarith only [hk0])
      (show 0 < k + 41 / 100 by linarith only [hk0])
    have hq := mul_nonneg (show 0 ≤ 27 / 25 - nearDiagonalNorm k by linarith only [le_of_not_gt h])
      (show 0 ≤ 27 / 25 + nearDiagonalNorm k by linarith only [hb])
    nlinarith only [hp, hq, hbsq]
  have hhi : nearDiagonalNorm k < 13 / 12 := by
    by_contra h
    have hp := mul_pos (show 0 < 29 / 70 - k by linarith only [hk1])
      (show 0 < 29 / 70 + k by linarith only [hk0])
    have hq := mul_nonneg (show 0 ≤ nearDiagonalNorm k - 13 / 12 by linarith only [le_of_not_gt h])
      (show 0 ≤ nearDiagonalNorm k + 13 / 12 by linarith only [hb])
    nlinarith only [hp, hq, hbsq]
  refine ⟨hlo, hhi, ?_⟩
  have hp := mul_pos (show 0 < 1 + k by linarith only [hk0]) (sub_pos.mpr hlo)
  nlinarith only [hp, hk0]

theorem wide_crossing_ge_apex {k u v b N : ℝ}
    (hk : 0 < k) (hk1 : k < 1 / 2) (hN : 1 ≤ N)
    (hm : 1 ≤ (u + v) / 2) (hb : b ≤ 1 - N + k * v) :
    (u - v) / 2 ≤ wideCrossing k u b := by
  apply (le_div_iff₀ (by linarith only [hk] : 0 < 1 + k)).mpr
  have hp := mul_nonneg (show 0 ≤ 1 - k by linarith only [hk1]) (sub_nonneg.mpr hm)
  nlinarith only [hp, hb, hN, hk1]

theorem wide_peak_fits {a h k N e b : ℝ}
    (hk0 : 41 / 100 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hN : 27 / 25 ≤ N) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 4)
    (hah : a + h ≤ 37 / 20) (he : e ≤ 1)
    (hb : 1 - h - N + k * a / 2 ≤ b) :
    widePeak k b (e + (a - N) / k) ≤ a / 2 := by
  have hk : 0 < k := by linarith only [hk0]
  have hInv := wide_offset_inverse hk hksq
  have hB : e + (a - N) / k = e + (a - N) * (k + 2) := by
    rw [div_eq_mul_one_div, hInv]
  have hbox := mul_le_mul_of_nonneg_left hah
    (show 0 ≤ 1 - k / 2 by linarith only [hk1])
  have htilt := mul_le_mul_of_nonneg_left hh1 (by linarith only [hk0] : 0 ≤ k / 2)
  have hnorm := mul_le_mul_of_nonneg_left hN (by linarith only [hk0] : 0 ≤ 1 + k)
  unfold widePeak
  apply (div_le_iff₀ (by linarith only [hk0] : 0 < 2 * (1 + k))).mpr
  rw [hB]
  nlinarith only [hbox, htilt, hnorm, hk0, he, hb]

theorem wide_loss_twice {k : ℝ} (hk : 0 < k) (u b B : ℝ) :
    2 * (wideGain k u b B - wideBaselineGain k u b) =
      B - b - 2 * (1 + k) * (u - k) := by
  unfold wideGain wideBaselineGain wideCrossing
  field_simp [(by linarith only [hk] : 1 + k ≠ 0)] <;> ring

theorem wide_loss_twice_le {a h k N e u b : ℝ}
    (hk : 0 < k) (hksq : k ^ 2 + 2 * k = 1)
    (hb : 1 - h - N + k * a / 2 ≤ b) :
    2 * (wideGain k u b (e + (a - N) / k) - wideBaselineGain k u b) ≤
      e + 2 * (1 + k) * (a - u) + h - 3 * k * a / 2 - 1 - (1 + k) * N + 2 * (1 + k) * k := by
  rw [wide_loss_twice hk, div_eq_mul_one_div, wide_offset_inverse hk hksq]
  nlinarith only [hb]

theorem wide_fitting_constant_neg {k N : ℝ}
    (hk : 2 / 5 < k) (hksq : k ^ 2 + 2 * k = 1) (hN : 3 / 2 < (1 + k) * N) :
    (2 * (1 + k) - 1) * (2 / 3) - (12 / 5) * k - (1 + k) * N + 2 * (1 + k) * k < 0 := by
  nlinarith only [hk, hksq, hN]

theorem wide_truncation_loss_sum_le {a h k N u v eR eL bR bL : ℝ}
    (ha : 8 / 5 ≤ a) (hh : 0 ≤ h)
    (hk0 : 2 / 5 < k) (hk1 : k < 1 / 2) (hksq : k ^ 2 + 2 * k = 1)
    (hN : 3 / 2 < (1 + k) * N)
    (hbR : 1 - h - N + k * a / 2 ≤ bR) (hbL : 1 - N + k * a / 2 ≤ bL)
    (heR : eR ≤ 1 - (a - u)) (heL : eL ≤ 1 - (a - v))
    (hwR : a - u ≤ 2 / 3 - h / 4) (hwL : a - v ≤ 2 / 3 + 3 * h / 4) :
    max (wideGain k u bR (eR + (a - N) / k) - wideBaselineGain k u bR) 0 +
      max (wideGain k v bL (eL + (a - N) / k) - wideBaselineGain k v bL) 0 ≤ h := by
  have hk : 0 < k := by linarith only [hk0]
  have hc : 0 ≤ 2 * (1 + k) - 1 := by linarith only [hk0]
  have hK := wide_fitting_constant_neg hk0 hksq hN
  have hR := wide_loss_twice_le hk hksq hbR
  have hL := wide_loss_twice_le (h := 0) hk hksq (by simpa only [sub_zero] using hbL)
  have hwa := mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ 3 * k / 2)
  have hwR' := mul_le_mul_of_nonneg_left hwR hc
  have hwL' := mul_le_mul_of_nonneg_left hwL hc
  have hRbound : max (wideGain k u bR (eR + (a - N) / k) - wideBaselineGain k u bR) 0 ≤
      (5 - 2 * (1 + k)) * h / 8 := by
    apply max_le
    · nlinarith only [hR, heR, hwR', hwa, hK]
    · exact div_nonneg (mul_nonneg (by linarith only [hk1]) hh) (by norm_num)
  have hLbound : max (wideGain k v bL (eL + (a - N) / k) - wideBaselineGain k v bL) 0 ≤
      3 * (2 * (1 + k) - 1) * h / 8 := by
    apply max_le
    · nlinarith only [hL, heL, hwL', hwa, hK]
    · positivity
  have hlast := mul_nonneg (show 0 ≤ 1 / 2 - k by linarith only [hk1]) hh
  nlinarith only [hRbound, hLbound, hlast]

def wideGainDemand (a m h : ℝ) : ℝ := 12 * a / 5 - 8 * m / 5 - 11 / 8 - 17 * h / 10

theorem wide_gain_sum_ge_demand {a h k N u v eR eL bR bL δR δL τ : ℝ}
    (ha : 0 ≤ a) (hh : 0 ≤ h) (hm : 0 ≤ (u + v) / 2)
    (hk0 : 41 / 100 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hN : N ≤ 13 / 12) (hE : 1 - h / 2 ≤ eR + eL)
    (hbR : bR = 1 - N + k * v - δL - τ) (hbL : bL = 1 - N + k * u - δR)
    (hτ : τ ≤ 3 * (1 - k) * h / 2)
    (hloss : max (wideGain k u bR (eR + (a - N) / k) - wideBaselineGain k u bR) 0 +
      max (wideGain k v bL (eL + (a - N) / k) - wideBaselineGain k v bL) 0 ≤ h) :
    wideGainDemand a ((u + v) / 2) h - (δR + δL) / 2 ≤
      wideTruncatedGain k u bR (eR + (a - N) / k) +
      wideTruncatedGain k v bL (eL + (a - N) / k) := by
  have hk : 0 < k := by linarith only [hk0]
  have hInv := wide_offset_inverse hk hksq
  have hBinv : (a - N) / k = (a - N) * (k + 2) := by rw [div_eq_mul_one_div, hInv]
  have hA := mul_nonneg ha (show 0 ≤ k - 2 / 5 by linarith only [hk0])
  have hM := mul_nonneg hm (show 0 ≤ k - 2 / 5 by linarith only [hk0])
  have hNb := mul_le_mul_of_nonneg_left hN (by linarith only [hk0] : 0 ≤ 3 + k)
  have hconstant : -11 / 8 ≤ 3 / 2 + 2 * k - (3 + k) * N := by
    nlinarith only [hNb, hk0]
  have hTilt := mul_nonneg hh (show 0 ≤ 3 * k / 4 - 3 / 10 by linarith only [hk0])
  rw [wideTruncatedGain_eq_sub_loss, wideTruncatedGain_eq_sub_loss]
  unfold wideGainDemand
  unfold wideGain at hloss ⊢
  rw [hBinv] at hloss ⊢
  rw [hbR, hbL] at hloss ⊢
  nlinarith only [hA, hM, hconstant, hE, hτ, hTilt, hloss]

theorem wide_positive_square_payment {k δR δL HR HL Q : ℝ}
    (hk : 0 < k) (hk1 : k ≤ 1 / 2) (hδR : 0 ≤ δR) (hδL : 0 ≤ δL)
    (hQ : Q ≤ HR + HL + (δR + δL) / 2) :
    (max Q 0) ^ 2 / 8 ≤ (δR ^ 2 + δL ^ 2) / (2 * k) +
      ((max HR 0) ^ 2 + (max HL 0) ^ 2) / (2 * (1 + k)) := by
  let A := max HR 0
  let B := max HL 0
  let D := (δR ^ 2 + δL ^ 2) / (2 * k)
  let G := (A ^ 2 + B ^ 2) / (2 * (1 + k))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hDid : 2 * k * D = δR ^ 2 + δL ^ 2 := mul_div_cancel₀ _ (by positivity)
  have hGid : 2 * (1 + k) * G = A ^ 2 + B ^ 2 := mul_div_cancel₀ _ (by positivity)
  have hDpay := mul_nonneg (show 0 ≤ 3 - 2 * k by linarith only [hk1]) hD
  have hGpay := mul_nonneg (show 0 ≤ 3 - 2 * (1 + k) by linarith only [hk1]) hG
  have hR : Q ≤ A + B + (δR + δL) / 2 := by
    have hA : HR ≤ A := le_max_left _ _
    have hB : HL ≤ B := le_max_left _ _
    linarith only [hQ, hA, hB]
  have hR0 : 0 ≤ A + B + (δR + δL) / 2 := by dsimp [A, B]; positivity
  have hQsq : (max Q 0) ^ 2 ≤ (A + B + (δR + δL) / 2) ^ 2 := by
    have hmax := max_le hR hR0
    have hprod := mul_nonneg (sub_nonneg.mpr hmax)
      (show 0 ≤ A + B + (δR + δL) / 2 + max Q 0 by positivity)
    nlinarith only [hprod]
  have hCauchy : (A + B + (δR + δL) / 2) ^ 2 ≤
      (5 / 2) * (A ^ 2 + B ^ 2 + δR ^ 2 + δL ^ 2) := by
    nlinarith only [sq_nonneg (A - B), sq_nonneg (δR - A / 2),
      sq_nonneg (δL - A / 2), sq_nonneg (δR - B / 2),
      sq_nonneg (δL - B / 2), sq_nonneg ((δL - δR) / 2)]
  change (max Q 0) ^ 2 / 8 ≤ D + G
  nlinarith only [hQsq, hCauchy, hDpay, hGpay, hDid, hGid, hD, hG]

def widePaidBound (a m h k : ℝ) : ℝ :=
  m + 1 / 4 - (m - k) ^ 2 - (21 / 64) * h - (max (wideGainDemand a m h) 0) ^ 2 / 8

theorem widePaidBound_le_base {a m h k : ℝ}
    (ha : 8 / 5 ≤ a) (hh : 0 ≤ h) (hm : a - 1 / 2 - h / 4 ≤ m)
    (hk0 : 41 / 100 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1) :
    widePaidBound a m h k ≤ (21 / 5) * k - 295081 / 320000 := by
  have hQ := positive_square_ge_tangent (wideGainDemand a m h)
    (by norm_num : (0 : ℝ) ≤ 141 / 200)
  have hA := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ a - 8 / 5 by linarith only [ha])
    (show 2 * k - 1341 / 1000 ≤ 0 by linarith only [hk1])
  have hM := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ m - a + 1 / 2 + h / 4 by linarith only [hm])
    (show 2 * k - 459 / 500 ≤ 0 by linarith only [hk1])
  have hH := mul_nonpos_of_nonneg_of_nonpos hh
    (show 201 / 1000 - k / 2 ≤ 0 by linarith only [hk0])
  unfold wideGainDemand at hQ
  unfold widePaidBound wideGainDemand
  nlinarith only [hQ, sq_nonneg (m - 11 / 10), hA, hM, hH, hksq]

theorem widePaidBound_lt {a m h k : ℝ}
    (ha : 8 / 5 ≤ a) (hh : 0 ≤ h) (hm : a - 1 / 2 - h / 4 ≤ m)
    (hk0 : 41 / 100 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1) :
    widePaidBound a m h k < (41 / 50 : ℝ) := by
  have h := widePaidBound_le_base ha hh hm hk0 hk1 hksq
  linarith only [h, hk1]

end AmbidextrousSofa
