module

public import AmbidextrousSofa.Analysis.ShortTailGeometry
public import AmbidextrousSofa.Analysis.ClippedTailIntegral

@[expose] public section

/-!
# Two literal additional niche tails

A nearby two-wall competitor above the diagonal niche floor adds an extra
triangle to that floor, up to the triangle's inner tip. The actual
companion support keeps the competitor above the triangle there. The two
tail heights of the short-width comparison meet the peak condition at
their inner tips.
-/

noncomputable section

namespace AmbidextrousSofa

theorem near_tail_add_floor_le {k E p A B x n : ℝ}
    (hk : 0 < k) (hk1 : k < 1) (hksq : k ^ 2 + 2 * k = 1)
    (hfloor : max (x - p) 0 ≤ n)
    (hcomp : E / k ≤ A - p) (hpeak : 0 < E → E - k * p ≤ B)
    (hwall : min ((A - x) / k) (B + k * x) ≤ n) :
    max (x - p) 0 + affineCutTriangle k E p x ≤ n := by
  rcases le_or_gt E 0 with hE | hE
  · rwa [affineCutTriangle_eq_zero_of_height_nonpos hk.le hk1.le hE, add_zero]
  rcases le_or_gt (p + E / (1 - k)) x with hx | hx
  · rwa [affineCutTriangle_eq_zero_of_right hk1 hx, add_zero]
  have hc := near_tail_companion_bound hk hk1 hksq hcomp
    (show x - p ≤ E / (1 - k) by linarith only [hx])
  rw [sub_sub_sub_cancel_right] at hc
  exact affineCutTriangle_add_floor_le hfloor
    ((le_min hc (by linarith only [hpeak hE])).trans hwall)

theorem shortLeftTailHeight_peak {h k v δ : ℝ}
    (hη : (2 / 25 : ℝ) ≤ 1 - nearDiagonalNorm k + k ^ 2)
    (hE : 0 < shortLeftTailHeight k h δ) :
    shortLeftTailHeight k h δ - k * (k - v + h) ≤
      1 - h + k * v - δ - nearDiagonalNorm k := by
  rw [shortLeftTailHeight, max_eq_left ((lt_max_iff.mp hE).resolve_right (lt_irrefl 0)).le]
  linarith only [hη]

theorem shortRightTailHeight_peak {k u δ : ℝ}
    (hη : (2 / 25 : ℝ) ≤ 1 - nearDiagonalNorm k + k ^ 2)
    (hE : 0 < shortRightTailHeight δ) :
    shortRightTailHeight δ - k * (k - u) ≤
      1 + k * u - δ - nearDiagonalNorm k := by
  rw [shortRightTailHeight, max_eq_left ((lt_max_iff.mp hE).resolve_right (lt_irrefl 0)).le]
  linarith only [hη]

end AmbidextrousSofa
