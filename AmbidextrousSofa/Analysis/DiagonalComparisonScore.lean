module

public import AmbidextrousSofa.Analysis.LowHeightScore
public import AmbidextrousSofa.Analysis.CapReflection
public import AmbidextrousSofa.Analysis.CapTranslation
public import AmbidextrousSofa.Analysis.ExposureMoments

@[expose] public section

/-!
# The actual diagonal comparison objective

Only the actual two-wall tent at pi/4 is charged in this auxiliary
objective. Every proper barrier whose range reaches pi/4 dominates it.
Its horizontal reflection and translation identities therefore provide
valid comparisons without reflecting an outgoing terminal wall.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def diagonalBarrier (U : Set Plane) (x : ℝ) : ℝ :=
  max (cornerWall U (Real.pi / 4) x) 0

def diagonalComparisonScore (U : Set Plane) : ℝ :=
  intervalSpatialScore (capRoof U) (diagonalBarrier U)
    (horizontalLeft U) (horizontalRight U)

theorem diagonalBarrier_nonneg (U : Set Plane) (x : ℝ) : 0 ≤ diagonalBarrier U x :=
  le_max_right _ _

theorem continuous_diagonalBarrier (U : Set Plane) : Continuous (diagonalBarrier U) := by
  unfold diagonalBarrier cornerWall firstWall secondWall
  fun_prop

theorem IsDownwardCap.diagonalBarrier_eq_tent {U : Set Plane} (hU : IsDownwardCap U) (x : ℝ) :
    diagonalBarrier U x = max ((diagonalRight U + diagonalLeft U) / 2 - Real.sqrt 2 -
      |x - (diagonalRight U - diagonalLeft U) / 2|) 0 := by
  rw [diagonalBarrier, cornerWall_pi_div_four_eq_tent hU]

theorem IsDownwardCap.diagonalBarrier_le_partialBarrier {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα0 : Real.pi / 4 ≤ α)
    (hαL : α ≤ Real.pi / 2) (x : ℝ) : diagonalBarrier U x ≤ partialBarrier U α x :=
  max_le (cornerWall_pi_div_four_le_partialBarrier hU.isCompact hα0 hαL x)
    (partialBarrier_nonneg _ _ _)

theorem IsDownwardCap.capScore_le_diagonalComparisonScore {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα0 : Real.pi / 4 ≤ α)
    (hαL : α ≤ Real.pi / 2) : capScore U α ≤ diagonalComparisonScore U := by
  rw [hU.capScore_eq_intervalSpatialScore, diagonalComparisonScore, intervalSpatialScore,
    intervalSpatialScore]
  exact sub_le_sub_left (intervalIntegral.integral_mono_on
    (by linarith [horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact])
    ((continuous_diagonalBarrier U).intervalIntegrable _ _)
    (hU.intervalIntegrable_partialBarrier (by linarith [Real.pi_pos]) hαL _ _)
    fun x _ => hU.diagonalBarrier_le_partialBarrier hα0 hαL x) _

theorem diagonalBarrier_horizontalMirror (U : Set Plane) (x : ℝ) :
    diagonalBarrier (horizontalMirror U) x = diagonalBarrier U (-x) := by
  rw [diagonalBarrier, diagonalBarrier, cornerWall_horizontalMirror,
    show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 by ring]

theorem diagonalComparisonScore_horizontalMirror {U : Set Plane} (hU : IsDownwardCap U) :
    diagonalComparisonScore (horizontalMirror U) = diagonalComparisonScore U := by
  unfold diagonalComparisonScore
  rw [horizontalLeft_horizontalMirror hU, horizontalRight_horizontalMirror hU,
    show capRoof (horizontalMirror U) = _ from funext (capRoof_horizontalMirror U),
    show diagonalBarrier (horizontalMirror U) = _ from funext (diagonalBarrier_horizontalMirror U),
    intervalSpatialScore_reflect]

theorem diagonalComparisonScore_centeredCap {U : Set Plane} (hU : IsDownwardCap U) :
    diagonalComparisonScore (centeredCap U) = diagonalComparisonScore U := by
  unfold diagonalComparisonScore centeredCap
  generalize -(horizontalLeft U + horizontalRight U) / 2 = d
  rw [horizontalLeft_horizontalTranslate hU, horizontalRight_horizontalTranslate hU,
    show capRoof (horizontalTranslate U d) = _ from funext (capRoof_horizontalTranslate U d),
    show diagonalBarrier (horizontalTranslate U d) = fun x => diagonalBarrier U (x - d) from
      funext fun x => by rw [diagonalBarrier, diagonalBarrier, cornerWall_horizontalTranslate hU],
    intervalSpatialScore_translate]

theorem diagonalComparisonScore_centered_quarters {U : Set Plane} {C : ℝ}
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C) :
    diagonalComparisonScore U = (∫ x in (-2 * C)..(-C), capRoof U x) +
      (∫ x in C..(2 * C), capRoof U x) - ∫ x in (-C)..C, diagonalBarrier U x := by
  rw [diagonalComparisonScore, hleft, hright, intervalSpatialScore,
    show -2 * C + (2 * C - -2 * C) / 4 = -C by ring,
    show 2 * C - (2 * C - -2 * C) / 4 = C by ring]

end AmbidextrousSofa
