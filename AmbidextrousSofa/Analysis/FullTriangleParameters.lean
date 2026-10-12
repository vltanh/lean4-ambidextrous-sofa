module

public import AmbidextrousSofa.Analysis.FullTriangleScalar
public import AmbidextrousSofa.Analysis.WideNicheGeometry

@[expose] public section

/-!
# Parameters of the actual three-angle niche comparison

Unnormalized support directions avoid any auxiliary lifted body. The
left diagonal parameter includes the actual middle height deficit, and
its nearby support is evaluated on the original cap. Every full niche
triangle and every floor-loss bound therefore uses original support and
endpoint data.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

def fullTriangleCos (k : ℝ) : ℝ := 1 / nearDiagonalNorm k

theorem fullTriangleCos_bounds {k : ℝ}
    (hk0 : diagonalOffsetLower < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1) :
    12 / 13 < fullTriangleCos k ∧ fullTriangleCos k < 73 / 79 := by
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  have hN := nearDiagonalNorm_pos k
  have hN2 := nearDiagonalNorm_sq k
  rw [fullTriangleCos, lt_div_iff₀ hN, div_lt_iff₀ hN]
  constructor <;> nlinarith

/-- The diagonal offset `k = √2 - 1` and the cosine of its nearby angle. -/
theorem fullTriangle_offset_bounds :
    diagonalOffsetLower < Real.sqrt 2 - 1 ∧ Real.sqrt 2 - 1 < 29 / 70 ∧
      (Real.sqrt 2 - 1) ^ 2 + 2 * (Real.sqrt 2 - 1) = 1 ∧
      12 / 13 < fullTriangleCos (Real.sqrt 2 - 1) ∧
      fullTriangleCos (Real.sqrt 2 - 1) < 73 / 79 := by
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  obtain ⟨hk0, -, hk1⟩ := sqrt_two_sub_one_bounds
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  have hksq := sqrt_two_sub_one_quadratic
  exact ⟨hk0, hk1, hksq, fullTriangleCos_bounds hk0 hk1 hksq⟩

/-- The nearby direction's unit-norm identity keeps its cosine coupled to the diagonal offset. -/
theorem fullTriangleCos_quadratic {k : ℝ} (hksq : k ^ 2 + 2 * k = 1) :
    fullTriangleCos k ^ 2 * (2 - 2 * k) = 1 := by
  have hN := nearDiagonalNorm_pos k
  have hN2 := nearDiagonalNorm_sq k
  unfold fullTriangleCos
  field_simp
  nlinarith only [hN2, hksq]


theorem fullTriangle_norm_identities {k : ℝ} (hk : 0 < k)
    (hksq : k ^ 2 + 2 * k = 1) :
    nearDiagonalNorm k / k = 2 * (1 + k) * fullTriangleCos k ∧
      nearDiagonalNorm k * (k + 3) = 4 * fullTriangleCos k := by
  have hN := (nearDiagonalNorm_pos k).ne'
  have hN2 := nearDiagonalNorm_sq k
  rw [fullTriangleCos, mul_one_div, mul_one_div, div_eq_div_iff hk.ne' hN, eq_div_iff hN]
  exact ⟨by linear_combination hN2 - hksq, by linear_combination (k + 3) * hN2 + (k + 1) * hksq⟩

theorem fullTriangle_outer_zero_le {a e k u : ℝ} (hk : 0 < k)
    (hksq : k ^ 2 + 2 * k = 1) (he : e ≤ 1 - (a - u)) :
    fullTriangleRightZero k u (wideEndpointIntercept a e k) ≤
      1 + a - 2 * fullTriangleCos k := by
  rw [fullTriangleRightZero, wideEndpointIntercept, div_le_iff₀ (by linarith), sub_div,
    div_diagonal_offset hk hksq a, (fullTriangle_norm_identities hk hksq).1]
  linarith only [he]

theorem fullTriangle_floor_loss_le_endpoint {a e k u : ℝ} (hk : 0 < k)
    (hksq : k ^ 2 + 2 * k = 1) (he : e ≤ 1 - (a - u)) :
    max (fullTriangleRightZero k u (wideEndpointIntercept a e k) - (u - k)) 0 ≤
      max (a - u - (2 * fullTriangleCos k - (1 + k))) 0 :=
  max_le_max (by linarith only [fullTriangle_outer_zero_le hk hksq he]) le_rfl

/-- Signed endpoint-depth squares dominate the clipped floor losses,
including when a depth bound is below the floor threshold. -/
theorem floor_loss_le_of_bounds {k t wR wL bR bL : ℝ} (hk : k ≤ 1) (hR : wR ≤ bR)
    (hL : wL ≤ bL) :
    (1 - k) / 2 * ((max (wR - t) 0) ^ 2 + (max (wL - t) 0) ^ 2) ≤
      (1 - k) / 2 * ((bR - t) ^ 2 + (bL - t) ^ 2) := by
  have hbound (w b : ℝ) (hw : w ≤ b) : (max (w - t) 0) ^ 2 ≤ (b - t) ^ 2 := by
    rcases le_total 0 (w - t) with hpos | hneg
    · rw [max_eq_left hpos]
      exact pow_le_pow_left₀ hpos (by linarith) 2
    · rw [max_eq_right hneg]
      simpa using sq_nonneg (b - t)
  exact mul_le_mul_of_nonneg_left (add_le_add (hbound wR bR hR) (hbound wL bL hL))
    (by linarith)

theorem fullTriangle_gain_sum {a eR eL h k u v bR bL δR δL : ℝ}
    (hk : 0 < k) (hksq : k ^ 2 + 2 * k = 1)
    (hbR : bR = 1 - nearDiagonalNorm k + k * v - h - δL)
    (hbL : bL = 1 - nearDiagonalNorm k + k * u - δR)
    (hEP : 1 - h / 2 ≤ eR + eL) :
    fullTriangleDemand a ((u + v) / 2) h k (fullTriangleCos k) ≤
      wideGain k u bR (wideEndpointIntercept a eR k) +
        wideGain k (v - h) bL (wideEndpointIntercept a eL k) + (δR + δL) / 2 := by
  rw [fullTriangleDemand, wideGain, wideGain, wideEndpointIntercept, wideEndpointIntercept,
    div_diagonal_offset hk hksq, hbR, hbL]
  linarith only [(fullTriangle_norm_identities hk hksq).2, hEP]

end AmbidextrousSofa
