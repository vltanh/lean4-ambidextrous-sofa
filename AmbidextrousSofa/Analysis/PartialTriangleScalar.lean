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

/-- The shared tilt payment reduces the proper correction to its zero-tilt corner. -/
theorem fullTriangleRelaxation_add_partial_loss_lt {a h k c u v : ℝ}
    (ha : 37 / 25 ≤ a) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 3)
    (hk : 0 < k) (hksq : k ^ 2 + 2 * k = 1)
    (hc : 0 < c) (hcsq : c ^ 2 * (2 - 2 * k) = 1)
    (hq : 0 ≤ (u + v - h) / 2 - k) :
    fullTriangleRelaxation a h k c u v + partialTriangleLoss h k c < referenceHalfAreaLower := by
  obtain ⟨hk0, hk1, hc0, hc1, -, -⟩ := triangle_parameter_bounds hk hksq hc hcsq
  obtain ⟨hs0, hs1⟩ := triangle_stationary_offset_bounds (by norm_num : (73 / 50 : ℝ) ≤ 37 / 25)
    le_rfl hk0 hk1 hc0 hc1
  have hbound := fullTriangleRelaxation_le_bound ha (by norm_num) hh0 hh1 hk0 hk1 hksq hs0 hs1 hq
  have ht : 2 / 5 ≤ k := by
    norm_num [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at hk0; linarith
  have hheight : fullTriangleBound (37 / 25) h k c + partialTriangleLoss h k c ≤
      triangleCornerScore (37 / 25) 0 k c (2 / 3) (2 / 3) 0 := by
    have hpay := triangle_tilt_payment (s := fullTriangleStationaryOffset (37 / 25) k c)
      (p := 0) (q := 2 / 3 - (2 * c - (1 + k)))
      (r := 0) (t := 2 / 3) (h0 := 0) (h := h) ht (by linarith)
      (by linarith) (by linarith) (by norm_num) hh0 (by norm_num) (by linarith)
    unfold fullTriangleBound partialTriangleLoss triangleCornerScore
    linarith only [hpay, hksq]
  have hcorner := triangleCornerScore_le_Newton (a := 37 / 25) (h := 0)
    (bR := 2 / 3) (bL := 2 / 3) (w := 0) hk hksq hc hcsq
    (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hcheck : triangleCornerScore (37 / 25) 0 diagonalOffsetUpper triangleCosUpper (2 / 3) (2 / 3) 0 < referenceHalfAreaLower := by
    norm_num [triangleCornerScore, fullTriangleStationaryOffset, triangleCosUpper, diagonalOffsetUpper, squareRootNewton,
      referenceHalfAreaLower, referenceRootLower, cubicBracketLower, cubicBracketUpper, cubic]
  linarith only [hbound, hheight, hcorner, hcheck]

end AmbidextrousSofa
