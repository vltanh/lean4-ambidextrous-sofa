module

public import AmbidextrousSofa.Analysis.DiagonalLowHeight
public import AmbidextrousSofa.Analysis.TopFacetEndpoints

@[expose] public section

/-!
# Excluding low middle endpoints at a canonical full maximum

The full score at angle `π / 2` is at most the diagonal comparison score, so
the diagonal comparison score of a full maximizer reaches the low-height
bound. Top insertion locates the endpoint on the rising side of an affine
middle roof at height one. Hence both endpoints of an affine middle roof of
a height-one global maximizer are strictly above one half.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem IsFullCapMaximizer.middle_endpoints_gt_half_of_affine
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    1 / 2 < capRoof U
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) ∧
    1 / 2 < capRoof U
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) := by
  obtain ⟨m, c, haffine⟩ := haffine
  exact hU.isCap.middle_endpoints_gt_half_of_diagonal (by linarith [hU.width_bounds.1, one_lt_M])
    (by linarith [lowHeightBound_lt_half_M, hU.reference_le,
      hU.isCap.capScore_le_diagonalComparisonScore (by linarith [Real.pi_pos]) le_rfl]) haffine
    (hU.middle_right_eq_one_of_affine_nonneg hheight · haffine)
    (hU.middle_left_eq_one_of_affine_nonpos hheight · haffine)

end AmbidextrousSofa
