module

public import AmbidextrousSofa.Analysis.DiagonalLowHeight
public import AmbidextrousSofa.Analysis.PartialTopInsertion

@[expose] public section

/-!
# Actual proper maxima have middle endpoints above one half

The diagonal comparison score bounds the original proper score at every
visited range reaching pi/4, so the diagonal comparison score of a joint
maximizer reaches the low-height bound. Top insertion supplies the
height-one endpoint in the actual orientation. The proper barrier and its
outgoing wall stay in their original orientation.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem IsJointCapMaximizer.middle_endpoints_gt_half_of_affine
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α) (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    1 / 2 < capRoof U
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) ∧
    1 / 2 < capRoof U
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) := by
  obtain ⟨m, c, haffine⟩ := haffine
  exact hU.isCap.middle_endpoints_gt_half_of_diagonal (by linarith [hU.width_bounds.1, one_lt_M])
    (by linarith [lowHeightBound_lt_half_M, hU.reference_le,
      hU.isCap.capScore_le_diagonalComparisonScore hU.angle_mem.1 hU.angle_mem.2]) haffine
    (hU.middle_right_eq_one_of_affine_nonneg hheight · haffine)
    (hU.middle_left_eq_one_of_affine_nonpos hheight · haffine)

end AmbidextrousSofa
