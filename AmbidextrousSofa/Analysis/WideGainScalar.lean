module

public import AmbidextrousSofa.Analysis.WideNichePieces

@[expose] public section

/-!
# Exact scalar payment for the two retained wide niche pieces

The truncation losses are bounded before the two positive heights are
combined with the exterior cuts. A rational quadratic inequality pays
the resulting positive square, and one global supporting plane excludes
the wide feasible region.
-/

noncomputable section

namespace AmbidextrousSofa

theorem wide_norm_rational_bounds {k : ℝ} (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70) :
    27 / 25 < nearDiagonalNorm k ∧ nearDiagonalNorm k < 13 / 12 ∧
      3 / 2 < (1 + k) * nearDiagonalNorm k := by
  have hlo : 27 / 25 < nearDiagonalNorm k := Real.lt_sqrt_of_sq_lt (by nlinarith)
  exact ⟨hlo, (Real.sqrt_lt' (by norm_num)).2 (by nlinarith),
    by linarith [mul_pos (sub_pos.2 hk0) (sub_pos.2 hlo)]⟩

/-- A support line at most `1 - N + k w - (1 - k) h` crosses the diagonal floor after its apex
once the diagonal midpoint is large enough. -/
theorem wide_crossing_after_apex {k u w h b N : ℝ} (hk : 0 < k) (hk1 : k < 29 / 70)
    (hN : 27 / 25 < N) (hh : 0 ≤ h) (hm : 179 / 200 ≤ (u + w) / 2)
    (hb : b ≤ 1 - N + k * w - (1 - k) * h) : (u - w) / 2 < wideCrossing k u b := by
  rw [wideCrossing, lt_div_iff₀ (by linarith only [hk])]
  linarith only [mul_nonneg (by linarith only [hk1] : (0 : ℝ) ≤ 1 - k) (sub_nonneg.mpr hm),
    mul_nonneg (by linarith only [hk1] : (0 : ℝ) ≤ 1 - k) hh, hb, hN, hk1]

theorem wide_peak_fits {a h k N e b : ℝ}
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hN : 27 / 25 ≤ N) (hh1 : h ≤ 1 / 4)
    (hah : a + h ≤ 37 / 20) (he : e ≤ 1)
    (hb : 1 - h - N + k * a / 2 ≤ b) :
    widePeak k b (e + (a - N) / k) ≤ a / 2 := by
  rw [widePeak, div_le_iff₀ (by linarith only [hk0])]
  linarith only [div_diagonal_offset (by linarith only [hk0]) hksq (a - N), hk0, he, hb,
    mul_le_mul_of_nonneg_left hah (show 0 ≤ 1 - k / 2 by linarith only [hk1]),
    mul_le_mul_of_nonneg_left hh1 (by linarith only [hk0] : 0 ≤ k / 2),
    mul_le_mul_of_nonneg_left hN (by linarith only [hk0] : 0 ≤ 1 + k)]

private theorem wide_loss_twice {k : ℝ} (hk : 0 < k) (u b B : ℝ) :
    2 * (wideGain k u b B - wideBaselineGain k u b) = B - b - 2 * (1 + k) * (u - k) := by
  unfold wideGain wideBaselineGain wideCrossing
  field_simp
  ring

theorem wide_truncation_loss_sum_le {a h k N u v eR eL bR bL : ℝ}
    (ha : 8 / 5 ≤ a) (hh : 0 ≤ h)
    (hk0 : 41 / 99 < k) (hk1 : k < 1 / 2) (hksq : k ^ 2 + 2 * k = 1)
    (hN : 3 / 2 < (1 + k) * N)
    (hbR : 1 - h - N + k * a / 2 ≤ bR) (hbL : 1 - N + k * a / 2 ≤ bL)
    (heR : eR ≤ 1 - (a - u)) (heL : eL ≤ 1 - (a - v))
    (hwR : a - u ≤ 2 / 3 - h / 4) (hwL : a - v ≤ 2 / 3 + 3 * h / 4) :
    max (wideGain k u bR (eR + (a - N) / k) - wideBaselineGain k u bR) 0 +
      max (wideGain k v bL (eL + (a - N) / k) - wideBaselineGain k v bL) 0 ≤ h := by
  have hk : 0 < k := by linarith only [hk0]
  have hc : 0 ≤ 2 * (1 + k) - 1 := by linarith only [hk0]
  have hdiv := div_diagonal_offset hk hksq (a - N)
  have hK : (2 * (1 + k) - 1) * (2 / 3) - (12 / 5) * k - (1 + k) * N + 2 * (1 + k) * k < 0 := by
    nlinarith only [hk0, hksq, hN]
  have hwa := mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ 3 * k / 2)
  refine (add_le_add (max_le ?_ (mul_nonneg (by linarith only [hk1]) hh : 0 ≤ (3 - 2 * k) / 8 * h))
    (max_le ?_ (mul_nonneg (by linarith only [hk0]) hh : 0 ≤ 3 * (1 + 2 * k) / 8 * h))).trans ?_
  · linarith only [wide_loss_twice hk u bR (eR + (a - N) / k), hdiv, hbR, heR, hwa, hK,
      mul_le_mul_of_nonneg_left hwR hc]
  · linarith only [wide_loss_twice hk v bL (eL + (a - N) / k), hdiv, hbL, heL, hwa, hK,
      mul_le_mul_of_nonneg_left hwL hc]
  · linarith only [mul_nonneg (show 0 ≤ 1 / 2 - k by linarith only [hk1]) hh]

def wideGainDemand (a m h : ℝ) : ℝ := 12 * a / 5 - 8 * m / 5 - 11 / 8 - 17 * h / 10

theorem wide_gain_sum_ge_demand {a h k N u v eR eL bR bL δR δL τ : ℝ}
    (ha : 0 ≤ a) (hh : 0 ≤ h) (hm : 0 ≤ (u + v) / 2)
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hN : N ≤ 13 / 12) (hE : 1 - h / 2 ≤ eR + eL)
    (hbR : bR = 1 - N + k * v - δL - τ) (hbL : bL = 1 - N + k * u - δR)
    (hτ : τ ≤ 3 * (1 - k) * h / 2)
    (hloss : max (wideGain k u bR (eR + (a - N) / k) - wideBaselineGain k u bR) 0 +
      max (wideGain k v bL (eL + (a - N) / k) - wideBaselineGain k v bL) 0 ≤ h) :
    wideGainDemand a ((u + v) / 2) h - (δR + δL) / 2 ≤
      wideTruncatedGain k u bR (eR + (a - N) / k) +
      wideTruncatedGain k v bL (eL + (a - N) / k) := by
  have hdiv := div_diagonal_offset (by linarith only [hk0]) hksq (a - N)
  rw [wideTruncatedGain_eq_sub_loss, wideTruncatedGain_eq_sub_loss, wideGainDemand]
  unfold wideGain at hloss ⊢
  subst hbR hbL
  linarith only [hdiv, hE, hτ, hloss, hk0, hk1,
    mul_nonneg ha (show 0 ≤ k - 2 / 5 by linarith only [hk0]),
    mul_nonneg hm (show 0 ≤ k - 2 / 5 by linarith only [hk0]),
    mul_le_mul_of_nonneg_left hN (by linarith only [hk0] : 0 ≤ 3 + k),
    mul_nonneg hh (show 0 ≤ 3 * k / 4 - 3 / 10 by linarith only [hk0])]

theorem wide_positive_square_payment {k δR δL HR HL Q : ℝ}
    (hk : 0 < k) (hk1 : k ≤ 1 / 2) (hδR : 0 ≤ δR) (hδL : 0 ≤ δL)
    (hQ : Q ≤ HR + HL + (δR + δL) / 2) :
    (max Q 0) ^ 2 / 8 ≤ (δR ^ 2 + δL ^ 2) / (2 * k) +
      ((max HR 0) ^ 2 + (max HL 0) ^ 2) / (2 * (1 + k)) := by
  set A := max HR 0
  set B := max HL 0
  have hS := pow_le_pow_left₀ (le_max_right Q 0) (max_le
    (by linarith only [hQ, le_max_left HR 0, le_max_left HL 0])
    (by positivity) : max Q 0 ≤ A + B + (δR + δL) / 2) 2
  have hD := le_div_self (by positivity : 0 ≤ δR ^ 2 + δL ^ 2) (by positivity : 0 < 2 * k)
    (by linarith only [hk1])
  have hG := div_le_div_of_nonneg_left (by positivity : 0 ≤ A ^ 2 + B ^ 2)
    (by positivity : (0 : ℝ) < 2 * (1 + k)) (by linarith only [hk1] : 2 * (1 + k) ≤ 3)
  -- Cauchy–Schwarz with weights `1, 1, 1/2, 1/2`.
  linarith only [hS, hD, hG, sq_nonneg (A - B), sq_nonneg (δR - A / 2), sq_nonneg (δL - A / 2),
    sq_nonneg (δR - B / 2), sq_nonneg (δL - B / 2), sq_nonneg ((δL - δR) / 2), sq_nonneg A,
    sq_nonneg B, sq_nonneg δR, sq_nonneg δL]

def widePaidBound (a m h k : ℝ) : ℝ :=
  m + 1 / 4 - (m - k) ^ 2 - (21 / 64) * h - (max (wideGainDemand a m h) 0) ^ 2 / 8

theorem widePaidBound_lt {a m h k : ℝ}
    (ha : 8 / 5 ≤ a) (hh : 0 ≤ h) (hm : a - 1 / 2 - h / 4 ≤ m)
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1) :
    widePaidBound a m h k < (41 / 50 : ℝ) := by
  have hQ := positive_square_ge_tangent (wideGainDemand a m h)
    (by norm_num : (0 : ℝ) ≤ 141 / 200)
  unfold widePaidBound
  unfold wideGainDemand at hQ ⊢
  linarith only [hQ, sq_nonneg (m - 11 / 10), hksq, hk1,
    mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ a - 8 / 5 by linarith only [ha])
      (show 2 * k - 1341 / 1000 ≤ 0 by linarith only [hk1]),
    mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ m - a + 1 / 2 + h / 4 by linarith only [hm])
      (show 2 * k - 459 / 500 ≤ 0 by linarith only [hk1]),
    mul_nonpos_of_nonneg_of_nonpos hh (show 201 / 1000 - k / 2 ≤ 0 by linarith only [hk0])]

end AmbidextrousSofa
