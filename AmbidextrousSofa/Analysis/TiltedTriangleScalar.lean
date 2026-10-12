module

public import AmbidextrousSofa.Analysis.FullTriangleScalar
public import AmbidextrousSofa.Analysis.TiltedRadiusWidth

@[expose] public section

/-!
# The sharper triangle bound in the remaining tilted strip

The complete jointly concave support relaxation is compared at width
the Newton lower enclosure of the radius-defined width. Actual zero left endpoint niche later supplies the asymmetric
floor correction. All clipping cases remain present in the relaxation;
the comparison point alone is unclipped. The same tilt-payment and Newton-corner comparison as the full and
proper floor corrections applies here.
-/

noncomputable section

attribute [local simp]
  AmbidextrousSofa.Analysis.tiltedBalanceMomentum
  AmbidextrousSofa.Analysis.tiltedBalanceFloorOffset
  AmbidextrousSofa.Analysis.tiltedBalanceGap
  AmbidextrousSofa.Analysis.tiltedBalanceDerivative
  AmbidextrousSofa.Analysis.tiltedBalanceLowerStep
  AmbidextrousSofa.Analysis.tiltedBalanceUpperStep
  AmbidextrousSofa.Analysis.tiltedBalanceLower₁
  AmbidextrousSofa.Analysis.tiltedBalanceUpper₁
  AmbidextrousSofa.Analysis.tiltedBalanceLower₂
  AmbidextrousSofa.Analysis.tiltedBalanceUpper₂
  AmbidextrousSofa.Analysis.tiltedBalanceLower
  AmbidextrousSofa.Analysis.tiltedBalanceUpper

namespace AmbidextrousSofa

def tiltedTriangleLoss (h k c : ℝ) : ℝ :=
  ((1 - k) / 2) *
    ((1 / 2 - (2 * c - (1 + k)) - h / 4) ^ 2 +
      (1 / 2 - (2 * c - (1 + k)) + 1 / 12 + 3 * h / 4) ^ 2)

/-- The shared tilt payment reduces the dry-endpoint correction to zero tilt
at the radius-defined width. No height subdivision is needed. -/
theorem tiltedTriangleRelaxation_add_loss_lt {a h k c u v : ℝ}
    (ha : 2 * Analysis.tiltedRadiusWidth ≤ a) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 3)
    (hk : 0 < k) (hksq : k ^ 2 + 2 * k = 1)
    (hc : 0 < c) (hcsq : c ^ 2 * (2 - 2 * k) = 1)
    (hq : 0 ≤ (u + v - h) / 2 - k) :
    fullTriangleRelaxation a h k c u v + tiltedTriangleLoss h k c < referenceHalfAreaLower := by
  let a0 : ℝ := 2 * Analysis.tiltedRadiusSpanLower / 3
  have ha0 : (73 / 50 : ℝ) ≤ a0 := Analysis.tiltedRadius_comparison_brackets.1
  have ha1 : a0 ≤ (37 / 25 : ℝ) := Analysis.tiltedRadius_comparison_brackets.2.1
  have hwidth : a0 ≤ a := by
    have h := Analysis.tiltedRadiusWidth_bounds.1
    dsimp only [a0]
    linarith
  obtain ⟨hk0, hk1, hc0, hc1, -, -⟩ := triangle_parameter_bounds hk hksq hc hcsq
  obtain ⟨hs0, hs1⟩ := triangle_stationary_offset_bounds ha0 ha1 hk0 hk1 hc0 hc1
  have hbound := fullTriangleRelaxation_le_bound hwidth ha0 hh0 hh1 hk0 hk1 hksq hs0 hs1 hq
  have ht : 2 / 5 ≤ k := by
    norm_num [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at hk0; linarith
  have hheight : fullTriangleBound a0 h k c + tiltedTriangleLoss h k c ≤
      triangleCornerScore a0 0 k c (1 / 2) (7 / 12) 1 := by
    have hpay := triangle_tilt_payment (s := fullTriangleStationaryOffset a0 k c)
      (p := 1 / 2 - (2 * c - (1 + k))) (q := 7 / 12 - (2 * c - (1 + k)))
      (r := -1 / 4) (t := 3 / 4) (h0 := 0) (h := h) ht (by linarith)
      (by linarith) (by linarith) (by norm_num) hh0 (by norm_num) (by linarith)
    unfold fullTriangleBound tiltedTriangleLoss triangleCornerScore
    linarith only [hpay, hksq]
  have hcorner := triangleCornerScore_le_Newton (a := a0) (h := 0)
    (bR := 1 / 2) (bL := 7 / 12) (w := 1) hk hksq hc hcsq
    ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hcheck : triangleCornerScore a0 0 diagonalOffsetUpper triangleCosUpper
      (1 / 2) (7 / 12) 1 < referenceHalfAreaLower := by
    norm_num [a0, triangleCornerScore, fullTriangleStationaryOffset, triangleCosUpper,
      diagonalOffsetUpper, squareRootNewton, Analysis.tiltedRadiusSpanLower,
      Analysis.tiltedRadiusSpanUpper, Analysis.tiltedRadiusSquare, Analysis.tiltedRadiusMomentum,
      referenceHalfAreaLower, referenceRootLower, cubicBracketLower, cubicBracketUpper, cubic]
  linarith only [hbound, hheight, hcorner, hcheck]

end AmbidextrousSofa
