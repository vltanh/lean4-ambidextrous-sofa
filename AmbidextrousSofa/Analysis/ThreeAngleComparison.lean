module

public import AmbidextrousSofa.Analysis.DiagonalComparisonScore
public import AmbidextrousSofa.Analysis.NearDiagonalWalls
public import AmbidextrousSofa.Analysis.InitialAngleExclusion

@[expose] public section

/-!
# A literal three-angle comparison objective

The objective charges the three-angle barrier, the maximum of precisely
three actual two-wall corners. Reflection exchanges the two nearby corners
and preserves the diagonal corner. Every sufficiently long proper barrier
dominates this same finite barrier, with its original outgoing wall
retained, and every joint maximizer turns far enough.
-/

noncomputable section

namespace AmbidextrousSofa

def threeAngleComparisonScore (U : Set Plane) : ℝ :=
  intervalSpatialScore (capRoof U) (threeAngleBarrier U)
    (horizontalLeft U) (horizontalRight U)

theorem IsJointCapMaximizer.threeAngle_last_lt_terminal {U : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) :
    Real.pi / 2 - Real.arctan (Real.sqrt 2 - 1) < α := by
  have hk := sqrt_two_sub_one_bounds.1
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  rw [← Real.arctan_inv_of_pos (by linarith only [hk])]
  refine (Real.arctan_strictMono ?_).trans hU.terminal_angle_gt_arctan_eight_thirds
  rw [inv_eq_one_div, div_lt_iff₀ (by linarith only [hk])]
  linarith only [hk]

theorem IsDownwardCap.capScore_le_threeAngleComparisonScore {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ}
    (hnear : Real.pi / 2 - Real.arctan (Real.sqrt 2 - 1) ≤ α)
    (hαL : α ≤ Real.pi / 2) : capScore U α ≤ threeAngleComparisonScore U :=
  hU.capScore_le_threeAngleScore hnear hαL

theorem threeAngleComparisonScore_horizontalMirror {U : Set Plane} (hU : IsDownwardCap U) :
    threeAngleComparisonScore (horizontalMirror U) = threeAngleComparisonScore U := by
  have hbarrier : threeAngleBarrier (horizontalMirror U) = fun x => threeAngleBarrier U (-x) := by
    funext x
    rw [threeAngleBarrier, threeAngleBarrier, diagonalBarrier_horizontalMirror,
      cornerWall_horizontalMirror, cornerWall_horizontalMirror, sub_sub_cancel,
      max_comm (cornerWall U (Real.pi / 2 - _) _)]
  unfold threeAngleComparisonScore
  rw [horizontalLeft_horizontalMirror hU, horizontalRight_horizontalMirror hU,
    funext (capRoof_horizontalMirror U), hbarrier, intervalSpatialScore_reflect]

end AmbidextrousSofa
