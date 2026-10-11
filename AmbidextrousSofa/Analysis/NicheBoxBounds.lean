module

public import AmbidextrousSofa.Analysis.NicheWings

@[expose] public section

/-!
# Exact middle endpoint niche bounds from the actual box

A unit-circle estimate `A cos + (1 - N) sin ≤ 1` bounds one entire inner
wall at each middle endpoint by `N` whenever the quarter-width is at most
`A`. With coefficients three and four, the full swept niche there is at
most two fifths whenever the quarter-width is at most four fifths. No
selected sources or regularity are used.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem IsDownwardCap.middle_niche_le_of_endpoints
    {U : Set Plane} (hU : IsDownwardCap U) {C A N : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C) (hC : C ≤ A) (hN : 0 ≤ N)
    (hcircle : ∀ s c : ℝ, c ^ 2 + s ^ 2 = 1 → A * c + (1 - N) * s ≤ 1) :
    sweptNiche U (Real.pi / 2) (-C) ≤ N ∧ sweptNiche U (Real.pi / 2) C ≤ N := by
  have hbox := hU.subset_centeredBox_of_endpoints hl hr
  refine ⟨sweptNiche_le_of_forall (by positivity) hN fun θ h => ?_,
    sweptNiche_le_of_forall (by positivity) hN fun θ h => ?_⟩ <;>
    obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter h
  · refine (min_le_right _ _).trans ?_
    rw [secondWall, div_le_iff₀ hc]
    linarith [hU.support_companionNormal_le_centeredBox hbox hs.le hc.le,
      mul_le_mul_of_nonneg_right hC hs.le, hcircle _ _ (Real.sin_sq_add_cos_sq θ)]
  · refine (min_le_left _ _).trans ?_
    rw [firstWall, div_le_iff₀ hs]
    linarith [hU.support_unitNormal_le_centeredBox hbox hs.le hc.le,
      mul_le_mul_of_nonneg_right hC hc.le, hcircle _ _ (Real.cos_sq_add_sin_sq θ)]

theorem IsDownwardCap.middle_niche_le_two_fifths_of_endpoints
    {U : Set Plane} (hU : IsDownwardCap U) {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : C ≤ 4 / 5) :
    sweptNiche U (Real.pi / 2) (-C) ≤ 2 / 5 ∧
      sweptNiche U (Real.pi / 2) C ≤ 2 / 5 :=
  hU.middle_niche_le_of_endpoints hl hr hC (by norm_num) fun s c _ => by
    nlinarith [sq_nonneg (3 * c - 4 * s), sq_nonneg (4 * c + 3 * s - 5)]

end AmbidextrousSofa
