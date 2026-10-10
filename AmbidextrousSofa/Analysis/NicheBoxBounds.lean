import AmbidextrousSofa.Analysis.NicheWings

/-!
# Exact middle endpoint niche bounds from the actual box

The rational unit-circle estimate with coefficients three and four bounds
one entire inner wall at each middle endpoint. Thus the full swept niche
there is at most two fifths whenever the quarter-width is at most four
fifths. No selected sources or regularity are used.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem three_four_circle_bound {s c : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c)
    (hcircle : c ^ 2 + s ^ 2 = 1) : (4 / 5) * c + (3 / 5) * s ≤ 1 := by
  have hsq : (4 * c + 3 * s) ^ 2 ≤ 25 := by
    nlinarith [sq_nonneg (3 * c - 4 * s)]
  by_contra hnot
  have hhigh : 5 < 4 * c + 3 * s := by linarith
  have hprod := mul_pos (sub_pos.mpr hhigh)
    (by linarith : 0 < 4 * c + 3 * s + 5)
  nlinarith

theorem IsDownwardCap.middle_niche_le_two_fifths_of_box
    {U : Set Plane} (hU : IsDownwardCap U) {C : ℝ}
    (hbox : U ⊆ Icc (-2 * C) (2 * C) ×ˢ Icc (0 : ℝ) 1) (hC : C ≤ 4 / 5) :
    sweptNiche U (Real.pi / 2) (-C) ≤ 2 / 5 ∧
      sweptNiche U (Real.pi / 2) C ≤ 2 / 5 := by
  constructor
  · apply sweptNiche_le_of_forall (by linarith [Real.pi_pos]) (by norm_num)
    intro θ hθ
    have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hsupport := hU.support_companionNormal_le_centeredBox hbox hs.le hc.le
    have hcmul := mul_le_mul_of_nonneg_right hC hs.le
    have hcircle := three_four_circle_bound hc.le hs.le
      (by linarith [Real.cos_sq_add_sin_sq θ])
    apply (min_le_right (firstWall U θ (-C)) (secondWall U θ (-C))).trans
    rw [secondWall, div_le_iff₀ hc]
    nlinarith
  · apply sweptNiche_le_of_forall (by linarith [Real.pi_pos]) (by norm_num)
    intro θ hθ
    have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hsupport := hU.support_unitNormal_le_centeredBox hbox hs.le hc.le
    have hcmul := mul_le_mul_of_nonneg_right hC hc.le
    have hcircle := three_four_circle_bound hs.le hc.le (Real.cos_sq_add_sin_sq θ)
    apply (min_le_left (firstWall U θ C) (secondWall U θ C)).trans
    rw [firstWall, div_le_iff₀ hs]
    nlinarith

theorem IsDownwardCap.middle_niche_le_two_fifths_of_endpoints
    {U : Set Plane} (hU : IsDownwardCap U) {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : C ≤ 4 / 5) :
    sweptNiche U (Real.pi / 2) (-C) ≤ 2 / 5 ∧
      sweptNiche U (Real.pi / 2) C ≤ 2 / 5 :=
  hU.middle_niche_le_two_fifths_of_box (hU.subset_centeredBox_of_endpoints hl hr) hC

end AmbidextrousSofa
