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
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- A joint positive-floor estimate. If both deficits exceed the threshold,
their sum pays the two positive parts; otherwise the larger coordinate
bound suffices. Thus no separate estimate is summed twice. -/
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
  rw [partialTriangleLoss]
  generalize 2 * c - (1 + k) = t at *
  have hx := le_max_right (wR - t) 0
  have hy := le_max_right (wL - t) 0
  have htotal : max (wR - t) 0 + max (wL - t) 0 ≤ 2 / 3 - t + 2 * h / 3 := by
    rcases max_choice (wR - t) 0 with h1 | h1 <;> rcases max_choice (wL - t) 0 with h2 | h2 <;>
      rw [h1, h2] <;> linarith
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  linarith [mul_nonneg hx hy, pow_le_pow_left₀ (add_nonneg hx hy) htotal 2]

/-- The complete proper floor correction retains a negative tilt variation.
The proof uses the exact quadratic expansion, without a differentiability
assumption or a numerical approximation. -/
theorem fullTriangleRelaxation_add_partial_loss_lt {a h k c u v : ℝ}
    (ha : 37 / 25 ≤ a) (hh0 : 0 ≤ h) (hh1 : h ≤ 17 / 50)
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hc0 : 923 / 1000 < c) (hc1 : c < 231 / 250)
    (hq : 0 ≤ (u + v - h) / 2 - k) :
    fullTriangleRelaxation a h k c u v + partialTriangleLoss h k c < (41 / 50 : ℝ) := by
  have hbound := fullTriangleRelaxation_le_bound ha hh0 hh1 hk0 hk1 hksq hc0 hc1 hq
  obtain ⟨hs0, hs1⟩ := fullTriangle_stationary_offset_bounds hk0 hk1 hc0 hc1
  rw [fullTriangleBound] at hbound
  rw [partialTriangleLoss]
  generalize fullTriangleStationaryOffset (37 / 25) k c = s at hs0 hs1 hbound
  generalize hd : 2 / 3 - (2 * c - (1 + k)) = d
  have hd0 : 0 < d := by linarith only [hd, hc1, hk0]
  have hd1 : d < 47 / 200 := by linarith only [hd, hc0, hk1]
  have hell : -k / 2 + (1 - k) * s / 9 + 2 * (1 - k) * d / 3 < -1 / 20 := by
    linarith only [mul_pos (sub_pos.2 hk0) (sub_pos.2 hs0), mul_pos (sub_pos.2 hk0) hd0, hs1,
      hd1, hk0]
  have hq' : -1 / 8 - (1 - k) ^ 2 / 72 + 2 * (1 - k) / 9 < 1 / 120 := by
    linarith only [hksq, hk0]
  linarith only [hbound, hksq, hk1, hh0, mul_le_mul_of_nonneg_right hell.le hh0,
    mul_le_mul_of_nonneg_right hq'.le (sq_nonneg h), mul_nonneg hh0 (sub_nonneg.2 hh1),
    mul_pos (sub_pos.2 hs0) (by linarith only [hs0] : 0 < s + 703 / 1000),
    mul_le_mul_of_nonneg_right (by linarith only [hk0] : 1 - k ≤ 3 / 5) (sq_nonneg d),
    mul_pos (sub_pos.2 hd1) (by linarith only [hd0] : 0 < 47 / 200 + d)]

end AmbidextrousSofa
