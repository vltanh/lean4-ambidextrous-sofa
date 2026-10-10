module

public import AmbidextrousSofa.Analysis.FullTriangleScalar

@[expose] public section

/-!
# Joint floor payment for the proper three-angle width comparison

The actual proper endpoint identities give a sum constraint on the two
support deficits. Keeping that constraint pays both positive-floor losses
by one square. The full three-triangle supporting plane then gives the
same strict rational gap for every remaining middle tilt. No separate
upper bound on either endpoint niche is assumed.
-/

noncomputable section

namespace AmbidextrousSofa

def partialTriangleLoss (h k c : ℝ) : ℝ :=
  ((1 - k) / 2) * (2 / 3 - (2 * c - (1 + k)) + 2 * h / 3) ^ 2

/-- The linear consequences of the actual proper endpoint laws. -/
theorem partialTriangle_endpoint_lower_bounds {h eR eL qR qL : ℝ}
    (hqR : 0 ≤ qR) (hqL : 0 ≤ qL)
    (heR : eR = 1 / 2 + h / 4 + (3 * qR - qL) / 4)
    (heL : eL = 1 / 2 - 3 * h / 4 + (3 * qL - qR) / 4)
    (hR : eR ≤ 1) (hL : eL ≤ 1 - 3 * h / 2) :
    1 / 3 + h / 2 ≤ eR ∧ 1 / 3 - 2 * h / 3 ≤ eL ∧
      1 - h / 2 ≤ eR + eL := by
  constructor
  · linarith only [heR, heL, hL, hqR]
  constructor
  · linarith only [heR, heL, hR, hqL]
  · linarith only [heR, heL, hqR, hqL]

/-- A joint positive-floor estimate. If both deficits exceed the threshold,
their sum pays the two positive parts; otherwise the larger coordinate
bound suffices. Thus no separate estimate is summed twice. -/
theorem partialTriangle_joint_positive_square {h t wR wL : ℝ}
    (hh : 0 ≤ h) (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 3)
    (hR : wR ≤ 2 / 3 - h / 2) (hL : wL ≤ 2 / 3 + 2 * h / 3)
    (hsum : wR + wL ≤ 1 + h / 2) :
    (max (wR - t) 0) ^ 2 + (max (wL - t) 0) ^ 2 ≤
      (2 / 3 - t + 2 * h / 3) ^ 2 := by
  let B := 2 / 3 - t + 2 * h / 3
  have hB : 0 ≤ B := by dsimp [B]; linarith only [ht1, hh]
  have htotal : max (wR - t) 0 + max (wL - t) 0 ≤ B := by
    by_cases hr : wR ≤ t
    · rw [max_eq_right (sub_nonpos.mpr hr), zero_add]
      exact max_le (by dsimp [B]; linarith only [hL]) hB
    · by_cases hl : wL ≤ t
      · rw [max_eq_right (sub_nonpos.mpr hl), add_zero]
        exact max_le (by dsimp [B]; linarith only [hR, hh]) hB
      · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge hr)),
          max_eq_left (sub_nonneg.mpr (le_of_not_ge hl))]
        dsimp [B]
        linarith only [hsum, ht0, hh]
  have hsq := (sq_le_sq₀
    (add_nonneg (le_max_right (wR - t) 0) (le_max_right (wL - t) 0)) hB).mpr htotal
  have hprod := mul_nonneg (le_max_right (wR - t) 0) (le_max_right (wL - t) 0)
  change (max (wR - t) 0) ^ 2 + (max (wL - t) 0) ^ 2 ≤ B ^ 2
  nlinarith only [hsq, hprod]

theorem partialTriangle_floor_loss_le {h k c wR wL : ℝ}
    (hh : 0 ≤ h) (hk : k ≤ 1)
    (ht0 : 1 / 3 ≤ 2 * c - (1 + k))
    (ht1 : 2 * c - (1 + k) ≤ 2 / 3)
    (hR : wR ≤ 2 / 3 - h / 2) (hL : wL ≤ 2 / 3 + 2 * h / 3)
    (hsum : wR + wL ≤ 1 + h / 2) :
    ((1 - k) / 2) *
        ((max (wR - (2 * c - (1 + k))) 0) ^ 2 +
          (max (wL - (2 * c - (1 + k))) 0) ^ 2) ≤
      partialTriangleLoss h k c := by
  exact mul_le_mul_of_nonneg_left
    (partialTriangle_joint_positive_square hh ht0 ht1 hR hL hsum)
    (by linarith only [hk] : 0 ≤ (1 - k) / 2)

/-- The complete proper floor correction retains a negative tilt variation.
The proof uses the exact quadratic expansion, without a differentiability
assumption or a numerical approximation. -/
theorem fullTriangleBound_add_partial_loss_lt {h k c : ℝ}
    (hh0 : 0 ≤ h) (hh1 : h ≤ 17 / 50)
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hc0 : 923 / 1000 < c) (hc1 : c < 231 / 250) :
    fullTriangleBound (37 / 25) h k c + partialTriangleLoss h k c <
      (25811237 / 31500000 : ℝ) := by
  let s0 := fullTriangleStationaryOffset (37 / 25) k c
  let A := 1 - k
  let γ := (1 - k) / 2
  let D := 2 / 3 - (2 * c - (1 + k))
  let ell := -k / 2 + A * s0 / 9 + 4 * γ * D / 3
  let q := -1 / 8 - A ^ 2 / 72 + 4 * γ / 9
  have hs := fullTriangle_stationary_offset_bounds hk0 hk1 hc0 hc1
  have hA : 0 < A ∧ A < 3 / 5 := by
    dsimp [A]
    constructor <;> linarith only [hk0, hk1]
  have hγ : 0 < γ ∧ γ < 3 / 10 := by
    dsimp [γ]
    constructor <;> linarith only [hk0, hk1]
  have hD : 0 < D ∧ D < 47 / 200 := by
    dsimp [D]
    constructor <;> linarith only [hc0, hc1, hk0, hk1]
  have hAs : A * s0 < (3 / 5) * (71 / 100) :=
    mul_lt_mul hA.2 hs.2.le (by linarith only [hs.1] : 0 < s0) (by norm_num)
  have hγD : γ * D < (3 / 10) * (47 / 200) :=
    mul_lt_mul hγ.2 hD.2.le hD.1 (by norm_num)
  have hell : ell < -22 / 375 := by
    dsimp [ell]
    linarith only [hAs, hγD, hk0]
  have hq : q < 1 / 120 := by
    dsimp [q]
    linarith only [hγ.2, sq_nonneg A]
  have htilt : ell * h + q * h ^ 2 ≤ 0 := by
    have h1 := mul_le_mul_of_nonneg_right hell.le hh0
    have h2 := mul_le_mul_of_nonneg_right hq.le (sq_nonneg h)
    have h3 := mul_nonneg hh0 (sub_nonneg.mpr hh1)
    nlinarith only [h1, h2, h3, hh0]
  have hexpand : fullTriangleBound (37 / 25) h k c + partialTriangleLoss h k c =
      (37 / 25 - (37 / 25 - k) ^ 2 / 2 - (2 / 9) * s0 ^ 2 + γ * D ^ 2) +
        ell * h + q * h ^ 2 := by
    dsimp [fullTriangleBound, partialTriangleLoss, s0, A, γ, D, ell, q]
    ring
  have hB : (37 / 25 : ℝ) - (37 / 25 - k) ^ 2 / 2 = (62 / 25) * k - 72 / 625 := by
    nlinarith only [hksq]
  have hs2 : (703 / 1000 : ℝ) ^ 2 < s0 ^ 2 := by
    nlinarith only [mul_pos (sub_pos.mpr hs.1)
      (show 0 < s0 + 703 / 1000 by linarith only [hs.1])]
  have hD2 : D ^ 2 < (47 / 200 : ℝ) ^ 2 := by
    nlinarith only [mul_pos (sub_pos.mpr hD.2)
      (show 0 < 47 / 200 + D by linarith only [hD.1])]
  have hγD2 : γ * D ^ 2 < 17 / 1000 := by
    have hm := mul_le_mul_of_nonneg_right hγ.2.le (sq_nonneg D)
    nlinarith only [hm, hD2]
  rw [hexpand, hB]
  linarith only [htilt, hs2, hγD2, hk1]

theorem fullTriangleRelaxation_add_partial_loss_lt {a h k c u v : ℝ}
    (ha : 37 / 25 ≤ a) (hh0 : 0 ≤ h) (hh1 : h ≤ 17 / 50)
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hc0 : 923 / 1000 < c) (hc1 : c < 231 / 250)
    (hq : 0 ≤ (u + v - h) / 2 - k) :
    fullTriangleRelaxation a h k c u v + partialTriangleLoss h k c < (41 / 50 : ℝ) := by
  have hbound := fullTriangleRelaxation_le_bound ha hh0 hh1 hk0 hk1 hksq hc0 hc1 hq
  have hstrict := fullTriangleBound_add_partial_loss_lt hh0 hh1 hk0 hk1 hksq hc0 hc1
  linarith only [hbound, hstrict]

end AmbidextrousSofa
