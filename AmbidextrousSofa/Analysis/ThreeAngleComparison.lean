module

public import AmbidextrousSofa.Analysis.DiagonalComparisonScore
public import AmbidextrousSofa.Analysis.FullTriangleArea
public import AmbidextrousSofa.Analysis.ShortWidthExclusion
public import AmbidextrousSofa.Analysis.InitialAngleExclusion

@[expose] public section

/-!
# A literal three-angle comparison objective

The barrier here is the maximum of precisely three actual two-wall
corners. Reflection exchanges the two nearby corners and preserves the
diagonal corner. Every sufficiently long proper barrier dominates this
same finite barrier, with its original outgoing wall retained.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def threeAngleBarrier (U : Set Plane) (x : ℝ) : ℝ :=
  max (diagonalBarrier U x)
    (max (cornerWall U (Real.arctan (Real.sqrt 2 - 1)) x)
      (cornerWall U (Real.pi / 2 - Real.arctan (Real.sqrt 2 - 1)) x))

def threeAngleComparisonScore (U : Set Plane) : ℝ :=
  intervalSpatialScore (capRoof U) (threeAngleBarrier U)
    (horizontalLeft U) (horizontalRight U)

theorem threeAngleBarrier_nonneg (U : Set Plane) (x : ℝ) : 0 ≤ threeAngleBarrier U x :=
  (diagonalBarrier_nonneg U x).trans (le_max_left _ _)

theorem continuous_threeAngleBarrier (U : Set Plane) : Continuous (threeAngleBarrier U) := by
  unfold threeAngleBarrier diagonalBarrier cornerWall firstWall secondWall
  fun_prop

theorem diagonalBarrier_le_threeAngleBarrier (U : Set Plane) (x : ℝ) :
    diagonalBarrier U x ≤ threeAngleBarrier U x := le_max_left _ _

theorem first_corner_le_threeAngleBarrier (U : Set Plane) (x : ℝ) :
    cornerWall U (Real.arctan (Real.sqrt 2 - 1)) x ≤ threeAngleBarrier U x :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem last_corner_le_threeAngleBarrier (U : Set Plane) (x : ℝ) :
    cornerWall U (Real.pi / 2 - Real.arctan (Real.sqrt 2 - 1)) x ≤ threeAngleBarrier U x :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem IsJointCapMaximizer.threeAngle_last_lt_terminal {U : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) :
    Real.pi / 2 - Real.arctan (Real.sqrt 2 - 1) < α := by
  have hk : 2 / 5 < Real.sqrt 2 - 1 := sqrt_two_sub_one_strict_bounds.1
  rw [← Real.arctan_inv_of_pos (by linarith only [hk])]
  refine (Real.arctan_strictMono ?_).trans hU.terminal_angle_gt_arctan_eight_thirds
  rw [inv_eq_one_div, div_lt_iff₀ (by linarith only [hk])]
  linarith only [hk]

theorem IsDownwardCap.capScore_le_threeAngleComparisonScore {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ}
    (hnear : Real.pi / 2 - Real.arctan (Real.sqrt 2 - 1) ≤ α)
    (hαL : α ≤ Real.pi / 2) : capScore U α ≤ threeAngleComparisonScore U := by
  have hk := sqrt_two_sub_one_strict_bounds
  have hc := arctan_le_complement_arctan (k := Real.sqrt 2 - 1) (by linarith only [hk.2.2])
  have hpos := sub_pos.mpr (Real.arctan_lt_pi_div_two (Real.sqrt 2 - 1))
  have hle (x : ℝ) : threeAngleBarrier U x ≤ partialBarrier U α x :=
    max_le (hU.diagonalBarrier_le_partialBarrier (by linarith only [hc, hnear]) hαL x)
      (max_le (hU.cornerWall_le_partialBarrier_of_angle_le
        (Real.arctan_pos.mpr (by linarith only [hk.1])) (hc.trans hnear) hαL x)
        (hU.cornerWall_le_partialBarrier_of_angle_le hpos hnear hαL x))
  rw [hU.capScore_eq_intervalSpatialScore]
  refine sub_le_sub_left (intervalIntegral.integral_mono_on ?_
    ((continuous_threeAngleBarrier U).intervalIntegrable _ _)
    (hU.intervalIntegrable_partialBarrier (hpos.trans_le hnear) hαL _ _) fun x _ => hle x) _
  linarith only [horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact]

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

theorem threeAngleComparisonScore_centered {U : Set Plane} {a : ℝ}
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a) :
    threeAngleComparisonScore U =
      ((∫ x in (-a)..(-a / 2), capRoof U x) + ∫ x in (a / 2)..a, capRoof U x) -
        ∫ x in (-a / 2)..(a / 2), threeAngleBarrier U x := by
  rw [threeAngleComparisonScore, hl, hr, intervalSpatialScore,
    show -a + (a - -a) / 4 = -a / 2 by ring,
    show a - (a - -a) / 4 = a / 2 by ring]

end AmbidextrousSofa
