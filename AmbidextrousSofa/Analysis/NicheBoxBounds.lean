module

public import AmbidextrousSofa.Analysis.NicheWings

@[expose] public section

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

private theorem three_four_circle_bound {s c : ℝ} (hcircle : c ^ 2 + s ^ 2 = 1) :
    (4 / 5) * c + (3 / 5) * s ≤ 1 := by
  nlinarith [sq_nonneg (3 * c - 4 * s), sq_nonneg (4 * c + 3 * s - 5)]

theorem IsDownwardCap.middle_niche_le_two_fifths_of_box
    {U : Set Plane} (hU : IsDownwardCap U) {C : ℝ}
    (hbox : U ⊆ Icc (-2 * C) (2 * C) ×ˢ Icc (0 : ℝ) 1) (hC : C ≤ 4 / 5) :
    sweptNiche U (Real.pi / 2) (-C) ≤ 2 / 5 ∧
      sweptNiche U (Real.pi / 2) C ≤ 2 / 5 := by
  refine ⟨sweptNiche_le_of_forall (by positivity) (by norm_num) fun θ h => ?_,
    sweptNiche_le_of_forall (by positivity) (by norm_num) fun θ h => ?_⟩ <;>
    have hs := Real.sin_pos_of_pos_of_lt_pi h.1 (h.2.trans (half_lt_self Real.pi_pos)) <;>
    have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [h.1, Real.pi_pos], h.2⟩
  · refine (min_le_right _ _).trans ?_
    rw [secondWall, div_le_iff₀ hc]
    linarith [hU.support_companionNormal_le_centeredBox hbox hs.le hc.le,
      mul_le_mul_of_nonneg_right hC hs.le, three_four_circle_bound (Real.sin_sq_add_cos_sq θ)]
  · refine (min_le_left _ _).trans ?_
    rw [firstWall, div_le_iff₀ hs]
    linarith [hU.support_unitNormal_le_centeredBox hbox hs.le hc.le,
      mul_le_mul_of_nonneg_right hC hc.le, three_four_circle_bound (Real.cos_sq_add_sin_sq θ)]

theorem IsDownwardCap.middle_niche_le_two_fifths_of_endpoints
    {U : Set Plane} (hU : IsDownwardCap U) {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : C ≤ 4 / 5) :
    sweptNiche U (Real.pi / 2) (-C) ≤ 2 / 5 ∧
      sweptNiche U (Real.pi / 2) C ≤ 2 / 5 :=
  hU.middle_niche_le_two_fifths_of_box (hU.subset_centeredBox_of_endpoints hl hr) hC

end AmbidextrousSofa
