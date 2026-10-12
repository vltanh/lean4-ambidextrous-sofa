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

theorem wide_norm_rational_bounds {k : ℝ} (hk0 : diagonalOffsetLower < k) (hk1 : k < 29 / 70) :
    27 / 25 < nearDiagonalNorm k ∧ nearDiagonalNorm k < 13 / 12 ∧
      3 / 2 < (1 + k) * nearDiagonalNorm k := by
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  have hlo : 27 / 25 < nearDiagonalNorm k := Real.lt_sqrt_of_sq_lt (by nlinarith)
  exact ⟨hlo, (Real.sqrt_lt' (by norm_num)).2 (by nlinarith),
    by linarith [mul_pos (sub_pos.2 hk0) (sub_pos.2 hlo)]⟩

/-- A support line at most `1 - N + k w - (1 - k) h` crosses the diagonal floor after its apex
once the diagonal midpoint is large enough. -/
theorem wide_crossing_after_apex {k u w h b N : ℝ} (hk : 0 < k) (hk1 : k < 29 / 70)
    (hN : 27 / 25 < N) (hh : 0 ≤ h) (hm : 3 / 4 ≤ (u + w) / 2)
    (hb : b ≤ 1 - N + k * w - (1 - k) * h) : (u - w) / 2 < wideCrossing k u b := by
  rw [wideCrossing, lt_div_iff₀ (by linarith only [hk])]
  linarith only [mul_nonneg (by linarith only [hk1] : (0 : ℝ) ≤ 1 - k) (sub_nonneg.mpr hm),
    mul_nonneg (by linarith only [hk1] : (0 : ℝ) ≤ 1 - k) hh, hb, hN, hk1]

/-- The weighted span is exactly the condition that the nearby-angle peak fits. -/
theorem wide_peak_fits {a h k N e b : ℝ}
    (hk : 0 < k) (hksq : k ^ 2 + 2 * k = 1)
    (hspan : (1 - k / 2) * a + h ≤ (1 + k) * N) (he : e ≤ 1)
    (hb : 1 - h - N + k * a / 2 ≤ b) :
    widePeak k b (e + (a - N) / k) ≤ a / 2 := by
  rw [widePeak, div_le_iff₀ (by linarith only [hk])]
  linarith only [div_diagonal_offset hk hksq (a - N), he, hb, hspan]

private theorem wide_loss_twice {k : ℝ} (hk : 0 < k) (u b B : ℝ) :
    2 * (wideGain k u b B - wideBaselineGain k u b) = B - b - 2 * (1 + k) * (u - k) := by
  unfold wideGain wideBaselineGain wideCrossing
  field_simp
  ring

theorem wide_truncation_loss_sum_le {a h k N u v eR eL bR bL : ℝ}
    (ha : 8 / 5 ≤ a) (hh : 0 ≤ h)
    (hk0 : diagonalOffsetLower < k) (hk1 : k < 1 / 2) (hksq : k ^ 2 + 2 * k = 1)
    (hN : 3 / 2 < (1 + k) * N)
    (hbR : 1 - h - N + k * a / 2 ≤ bR) (hbL : 1 - N + k * a / 2 ≤ bL)
    (heR : eR ≤ 1 - (a - u)) (heL : eL ≤ 1 - (a - v))
    (hwR : a - u ≤ 2 / 3 - h / 4) (hwL : a - v ≤ 2 / 3 + 3 * h / 4) :
    max (wideGain k u bR (eR + (a - N) / k) - wideBaselineGain k u bR) 0 +
      max (wideGain k v bL (eL + (a - N) / k) - wideBaselineGain k v bL) 0 ≤ h := by
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
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

/-- The exact sum of the two retained peak heights, from the endpoint
height budget, the companion walls, and the tilt and truncation losses. -/
def wideGainDemand (a m h k N : ℝ) : ℝ :=
  (2 + k) * a + (k - 2) * m + 3 / 2 + 2 * k - (3 + k) * N - (2 - 3 * k / 4) * h

theorem wide_gain_sum_ge_demand {a h k N u v eR eL bR bL δR δL τ : ℝ}
    (hk : 0 < k) (hksq : k ^ 2 + 2 * k = 1) (hE : 1 - h / 2 ≤ eR + eL)
    (hbR : bR = 1 - N + k * v - δL - τ) (hbL : bL = 1 - N + k * u - δR)
    (hτ : τ ≤ 3 * (1 - k) * h / 2)
    (hloss : max (wideGain k u bR (eR + (a - N) / k) - wideBaselineGain k u bR) 0 +
      max (wideGain k v bL (eL + (a - N) / k) - wideBaselineGain k v bL) 0 ≤ h) :
    wideGainDemand a ((u + v) / 2) h k N - (δR + δL) / 2 ≤
      wideTruncatedGain k u bR (eR + (a - N) / k) +
      wideTruncatedGain k v bL (eL + (a - N) / k) := by
  have hdiv := div_diagonal_offset hk hksq (a - N)
  rw [wideTruncatedGain_eq_sub_loss, wideTruncatedGain_eq_sub_loss, wideGainDemand]
  unfold wideGain at hloss ⊢
  subst hbR hbL
  linarith only [hdiv, hE, hτ, hloss]

/-- Weighted Cauchy–Schwarz uses the exact prices of the two cuts and
retained half-triangles. Their reciprocal prices add to `4 + 5k`. -/
theorem wide_positive_square_payment {k δR δL HR HL Q : ℝ}
    (hk : 0 < k) (hδR : 0 ≤ δR) (hδL : 0 ≤ δL)
    (hQ : Q ≤ HR + HL + (δR + δL) / 2) :
    (max Q 0) ^ 2 / (4 + 5 * k) ≤ (δR ^ 2 + δL ^ 2) / (2 * k) +
      ((max HR 0) ^ 2 + (max HL 0) ^ 2) / (2 * (1 + k)) := by
  set A := max HR 0
  set B := max HL 0
  have hS := pow_le_pow_left₀ (le_max_right Q 0) (max_le
    (by linarith only [hQ, le_max_left HR 0, le_max_left HL 0])
    (by positivity) : max Q 0 ≤ A + B + (δR + δL) / 2) 2
  have hkr : 0 ≤ k * (1 + k) := by positivity
  have hform : 2 * k * (1 + k) * (A + B + (δR + δL) / 2) ^ 2 ≤
      (4 + 5 * k) * ((1 + k) * (δR ^ 2 + δL ^ 2) + k * (A ^ 2 + B ^ 2)) := by
    nlinarith only [mul_nonneg hkr (sq_nonneg (δR - δL)),
      mul_nonneg hkr (sq_nonneg (A - B)),
      sq_nonneg (2 * (1 + k) * δR - k * A), sq_nonneg (2 * (1 + k) * δR - k * B),
      sq_nonneg (2 * (1 + k) * δL - k * A), sq_nonneg (2 * (1 + k) * δL - k * B)]
  rw [div_add_div _ _ (by positivity) (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [hform, mul_le_mul_of_nonneg_left hS
    (by positivity : 0 ≤ 2 * k * (1 + k))]

def widePaidBound (a m h k N : ℝ) : ℝ :=
  m + 1 / 4 - (m - k) ^ 2 - (21 / 64) * h -
    (max (wideGainDemand a m h k N) 0) ^ 2 / (4 + 5 * k)

/-- Price the peak demand so that its tilt term cancels the direct tilt
loss. Completing the remaining midpoint square gives a uniform bound. -/
theorem widePaidBound_le_price {a a0 m h k N t : ℝ}
    (ha : a0 ≤ a) (hk : 0 < k) (hksq : k ^ 2 + 2 * k = 1)
    (ht : 0 ≤ t) (hprice : 2 * t * (2 - 3 * k / 4) = 21 / 64) :
    widePaidBound a m h k N ≤
      k + 1 / 2 - 2 * t * ((2 + k) * a0 + 3 / 2 - 3 * k / 2 - (3 + k) * N) +
        (9 - k) * t ^ 2 := by
  have hQ := positive_square_ge_tangent (wideGainDemand a m h k N)
    (mul_nonneg (by positivity : 0 ≤ 4 + 5 * k) ht)
  have hd : 0 < 4 + 5 * k := by positivity
  have hpay : 2 * t * wideGainDemand a m h k N - (4 + 5 * k) * t ^ 2 ≤
      (max (wideGainDemand a m h k N) 0) ^ 2 / (4 + 5 * k) := by
    rw [le_div_iff₀ hd]
    nlinarith only [hQ]
  unfold widePaidBound wideGainDemand at hpay ⊢
  linear_combination hpay + sq_nonneg (m - (k + 1 / 2 + t * (2 - k))) +
    mul_nonneg (mul_nonneg ht (by linarith only [hk] : 0 ≤ 2 + k)) (sub_nonneg.mpr ha) * 2 +
    (t ^ 2 - 2 * t) * hksq + h * hprice

/-- The exact geometric prices leave a strict gap at the first wide width.
Root enclosures are only arithmetic witnesses for this formula comparison. -/
theorem widePaidBound_lt {a m h k N : ℝ}
    (ha : 8 / 5 ≤ a) (hk0 : diagonalOffsetLower < k) (hk1 : k < diagonalOffsetUpper)
    (hksq : k ^ 2 + 2 * k = 1) (hN : N ≤ 13 / 12) :
    widePaidBound a m h k N < (41 / 50 : ℝ) := by
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  let t : ℝ := (21 / 64) / (2 * (2 - 3 * k / 4))
  let tL : ℝ := (21 / 64) / (2 * (2 - 3 * diagonalOffsetLower / 4))
  let tU : ℝ := (21 / 64) / (2 * (2 - 3 * diagonalOffsetUpper / 4))
  let AL : ℝ := (2 + diagonalOffsetUpper) * (8 / 5) + 3 / 2 -
    3 * diagonalOffsetUpper / 2 - (3 + diagonalOffsetUpper) * (13 / 12)
  have hk : 0 < k := by norm_num [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at hk0; linarith
  have hd : 0 < 2 * (2 - 3 * k / 4) := by
    norm_num [diagonalOffsetUpper, squareRootNewton] at hk1; linarith
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hprice : 2 * t * (2 - 3 * k / 4) = 21 / 64 := by
    dsimp [t]
    field_simp [(by linarith only [hd] : (2 * 4 - 3 * k) ≠ 0)]
  have htl : tL ≤ t := by
    dsimp [tL, t]
    apply div_le_div_of_nonneg_left (by norm_num) hd
    linarith only [hk0]
  have htu : t ≤ tU := by
    dsimp [tU, t]
    apply div_le_div_of_nonneg_left (by norm_num)
      (by norm_num [diagonalOffsetUpper, squareRootNewton])
    linarith only [hk1]
  have hA : AL ≤ (2 + k) * (8 / 5) + 3 / 2 - 3 * k / 2 - (3 + k) * N := by
    dsimp [AL]
    nlinarith only [mul_nonneg (by linarith only [hk] : 0 ≤ 3 + k) (sub_nonneg.mpr hN), hk1]
  have hAL : 0 ≤ AL := by norm_num [AL, diagonalOffsetUpper, squareRootNewton]
  have htL : 0 ≤ tL := by norm_num [tL, diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton]
  have hcoef : 0 ≤ 9 - k := by norm_num [diagonalOffsetUpper, squareRootNewton] at hk1; linarith
  have hlin := mul_le_mul htl hA hAL ht
  have hquad : (9 - k) * t ^ 2 ≤ (9 - diagonalOffsetLower) * tU ^ 2 := by
    gcongr
  have hcert : diagonalOffsetUpper + 1 / 2 - 2 * tL * AL +
      (9 - diagonalOffsetLower) * tU ^ 2 < (41 / 50 : ℝ) := by
    norm_num [tL, tU, AL, diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton]
  have hbound := widePaidBound_le_price ha hk hksq ht hprice (m := m) (h := h) (N := N)
  norm_num [tL, tU, AL, diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at hlin hquad hcert
  nlinarith only [hbound, hlin, hquad, hcert, hk1]

end AmbidextrousSofa
