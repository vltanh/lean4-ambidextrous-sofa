module

public import AmbidextrousSofa.Analysis.DiagonalRelaxation
public import AmbidextrousSofa.Analysis.ShortWidthGeometryConstants

@[expose] public section

/-!
# Exact global bounds for the clipped diagonal relaxation

The positive square has a global supporting tangent. Each clipped tail
square is at most the squared displacement from an inactive tail at the
comparison point. These three elementary inequalities give a global
supporting plane for the full relaxation at every positive, unclipped
comparison point. The critical and constrained-critical comparisons
therefore require no differentiability across a clipping boundary.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem positive_square_ge_tangent (x : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    y ^ 2 + 2 * y * (x - y) ≤ (max x 0) ^ 2 := by
  linarith [sq_nonneg (max x 0 - y), mul_le_mul_of_nonneg_right (le_max_left x 0) hy]

theorem shifted_positive_square_le_displacement (x : ℝ) {c z : ℝ} (hz : z ≤ c) :
    (max (x - c) 0) ^ 2 ≤ (x - z) ^ 2 := by
  rcases le_total x c with hx | hx
  · rw [max_eq_right (sub_nonpos.mpr hx)]
    simpa using sq_nonneg (x - z)
  · rw [max_eq_left (sub_nonneg.mpr hx)]
    exact pow_le_pow_left₀ (sub_nonneg.mpr hx) (by linarith) 2

/-- The tangent of the clipped perspective term at slope `t`, valid when `c ≤ t - w`. -/
theorem clipped_perspective_ge_tangent {a h c t : ℝ}
    (ha : 0 < a) (hh : 0 ≤ h) (hha : h < a) (ht : t / a ≤ 3 / 2) (w : ℝ) (hct : c ≤ t - w) :
    2 * t * w - t ^ 2 + (-3 * t + t ^ 2 / a) * h ≤
      (w - 3 * h / 2) ^ 2 / (1 - h / a) - (max c 0) ^ 2 := by
  have hd : 0 < 1 - h / a := sub_pos.mpr ((div_lt_one ha).mpr hha)
  obtain ⟨q, hq⟩ : ∃ q, q = w - t - h * (3 / 2 - t / a) := ⟨_, rfl⟩
  have hqt : q ≤ w - t := hq ▸ sub_le_self _ (mul_nonneg hh (sub_nonneg.mpr ht))
  have hclip : max c 0 ^ 2 ≤ q ^ 2 := (pow_le_pow_left₀ (le_max_right _ _)
    (max_le (by linarith [neg_le_abs q]) (abs_nonneg q)) 2).trans_eq (sq_abs q)
  have hid : (w - 3 * h / 2) ^ 2 / (1 - h / a) =
      2 * t * w - t ^ 2 + (-3 * t + t ^ 2 / a) * h + q ^ 2 / (1 - h / a) := by
    rw [hq]
    field_simp [(sub_pos.mpr hha).ne']
    ring
  linarith [le_div_self (sq_nonneg q) hd (by linarith [div_nonneg hh ha.le] : 1 - h / a ≤ 1)]

theorem diagonalRelaxation_le_tangent (a h k u v u0 v0 : ℝ)
    (hq : 0 ≤ (u0 + v0 - h) / 2 - k)
    (hu0 : u0 ≤ k + a / 2) (hv0 : v0 ≤ h + k + a / 2) :
    diagonalRelaxation a h k u v ≤
      a - ((a - u0) ^ 2 + (a - v0) ^ 2) / 2 - a * h / 2 -
        ((u0 + v0 - h) / 2 - k) ^ 2 +
      (a - u0 - ((u0 + v0 - h) / 2 - k)) * (u - u0) +
      (a - v0 - ((u0 + v0 - h) / 2 - k)) * (v - v0) := by
  unfold diagonalRelaxation
  linarith [positive_square_ge_tangent ((u + v - h) / 2 - k) hq,
    shifted_positive_square_le_displacement (u - k) (by linarith : u0 - k ≤ a / 2),
    shifted_positive_square_le_displacement (v - h - k) (by linarith : v0 - h - k ≤ a / 2)]

theorem diagonalRelaxation_le_critical (a h k u v : ℝ)
    (hq : k + h / 2 ≤ a) (hleft : -2 * k / 3 ≤ h) (hright : h ≤ 2 * k) :
    diagonalRelaxation a h k u v ≤ a - (a - k) ^ 2 / 2 - k * h / 2 - h ^ 2 / 8 :=
  (diagonalRelaxation_le_tangent a h k u v ((a + k + h / 2) / 2) ((a + k + h / 2) / 2)
    (by linarith) (by linarith) (by linarith)).trans_eq (by ring)

theorem diagonal_critical_width_mono {a A k : ℝ} (ha : a ≤ A)
    (hA : A ≤ 1 + k) : a - (a - k) ^ 2 / 2 ≤ A - (A - k) ^ 2 / 2 := by
  linarith [mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ 1 + k - (A + a) / 2 by linarith)]

set_option maxHeartbeats 800000 in
/-- The high-score short-width region is forced into a small, unclipped
neighborhood. The thresholds are derived from the available nearby wall height. The conclusion is used by the actual extra-tail proof. -/
theorem short_diagonal_stability {a h k u v : ℝ}
    (ha0 : 41 / 50 ≤ a) (ha1 : a ≤ 1)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 37 / 100)
    (hk0 : diagonalOffsetLower < k) (hk1 : k < (diagonalOffsetUpper)) (hksq : k ^ 2 + 2 * k = 1)
    (hu : u ∈ Icc (a / 2) a) (hv : v ∈ Icc (a / 2) a)
    (hscore : referenceHalfAreaLower ≤ diagonalRelaxation a h k u v) :
    (1 - k ^ 2 / 4) < a ∧ h < (k ^ 2 / 4) ∧ u - a / 2 < shortTipThreshold k + h / 4 ∧
      v - a / 2 < shortTipThreshold k + h / 4 ∧ shortApexThreshold k < (u + v) / 2 - h / 4 := by
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  obtain ⟨hη, ht0, htk, hm0, hm1, hAcert, hHcert, hTcert, hMcert, -, -⟩ :=
    short_geometry_scalar_estimates hk0 hk1 hksq
  obtain ⟨hN0, hN1⟩ := nearDiagonalNorm_short_bounds hk0 hk1 hksq
  have htip : shortTipThreshold k = 3 * k + nearDiagonalNorm k - 2 := by
    rw [shortTipThreshold, shortTailHeight_eq hksq]; ring
  have hthalf : k / 2 < shortTipThreshold k := by
    rw [htip]; linarith
  norm_num [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton, shortNormUpper] at hN1
  have hcritical := diagonalRelaxation_le_critical a h k u v
    (by linarith) (by linarith) (by linarith)
  have hwidth := diagonal_critical_width_mono ha1
    (by linarith : (1 : ℝ) ≤ 1 + k)
  have hkh : 0 ≤ k * h := mul_nonneg (by linarith) hh0
  have ha : (1 - k ^ 2 / 4) < a := by
    by_contra! hbad
    linarith [diagonal_critical_width_mono hbad (by nlinarith : ((1 - k ^ 2 / 4) : ℝ) ≤ 1 + k),
      sq_nonneg h]
  have hh : h < (k ^ 2 / 4) := by
    by_contra! hbad
    nlinarith [mul_nonneg (by linarith : 0 ≤ k) (sub_nonneg.mpr hbad),
      mul_nonneg hh0 (sub_nonneg.mpr hbad)]
  have hclip : shortTipThreshold k + h / 4 < k := by
    rw [htip]
    nlinarith only [hk0, hk1, hksq, hh, hN1]
  -- Constrained-critical comparisons: tangent planes on the boundary of each excluded region.
  have hright : u - a / 2 < shortTipThreshold k + h / 4 := by
    by_contra! hbad
    linarith [diagonalRelaxation_le_tangent a h k u v (a / 2 + shortTipThreshold k + h / 4)
      (a / 2 + (2 * k - shortTipThreshold k) / 3 + h / 4) (by nlinarith) (by linarith) (by nlinarith),
      mul_nonpos_of_nonpos_of_nonneg (by linarith : (2 * k - 4 * (shortTipThreshold k)) / 3 ≤ 0)
        (by linarith : 0 ≤ u - (a / 2 + shortTipThreshold k + h / 4)), sq_nonneg h]
  have hleft : v - a / 2 < shortTipThreshold k + h / 4 := by
    by_contra! hbad
    linarith [diagonalRelaxation_le_tangent a h k u v (a / 2 + (2 * k - shortTipThreshold k) / 3 + h / 4)
      (a / 2 + shortTipThreshold k + h / 4) (by nlinarith) (by linarith) (by nlinarith),
      mul_nonpos_of_nonpos_of_nonneg (by linarith : (2 * k - 4 * (shortTipThreshold k)) / 3 ≤ 0)
        (by linarith : 0 ≤ v - (a / 2 + shortTipThreshold k + h / 4)), sq_nonneg h]
  have hq : 0 < (u + v - h) / 2 - k := by nlinarith [hu.1, hv.1]
  have hclipR : u - k - a / 2 < 0 := by linarith
  have hclipL : v - h - k - a / 2 < 0 := by linarith
  refine ⟨ha, hh, hright, hleft, ?_⟩
  by_contra! hm
  unfold diagonalRelaxation at hscore
  rw [max_eq_left hq.le, max_eq_right hclipR.le, max_eq_right hclipL.le] at hscore
  linarith [mul_nonneg (show 0 ≤ 2 * shortApexThreshold k - 1 by linarith)
      (sub_nonneg.2 ha1),
    mul_nonneg (show 0 ≤ 2 * (k - (2 * (shortApexThreshold k) - 1)) by linarith)
      (sub_nonneg.mpr hm),
    sq_nonneg ((a - 1) - ((u + v) / 2 - h / 4 - shortApexThreshold k)),
    sq_nonneg ((u + v) / 2 - h / 4 - shortApexThreshold k), sq_nonneg ((u - v) / 2), sq_nonneg h]

end AmbidextrousSofa
