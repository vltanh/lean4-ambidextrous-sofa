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
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hmono := intervalIntegral.integral_mono_on
    (show horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 ≤
      horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 by linarith)
    ((continuous_diagonalBarrier U).intervalIntegrable _ _)
    (hU.intervalIntegrable_partialBarrier (by linarith [Real.pi_pos]) hαL _ _)
    (fun x _ => hU.diagonalBarrier_le_partialBarrier hα0 hαL x)
  rw [hU.capScore_eq_intervalSpatialScore]
  unfold diagonalComparisonScore intervalSpatialScore
  linarith

theorem diagonalBarrier_horizontalMirror (U : Set Plane) (x : ℝ) :
    diagonalBarrier (horizontalMirror U) x = diagonalBarrier U (-x) := by
  rw [diagonalBarrier, cornerWall_horizontalMirror,
    show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 by ring]
  rfl

theorem diagonalComparisonScore_horizontalMirror {U : Set Plane} (hU : IsDownwardCap U) :
    diagonalComparisonScore (horizontalMirror U) = diagonalComparisonScore U := by
  unfold diagonalComparisonScore
  rw [horizontalLeft_horizontalMirror hU, horizontalRight_horizontalMirror hU]
  have hroof : capRoof (horizontalMirror U) = fun x => capRoof U (-x) :=
    funext (capRoof_horizontalMirror U)
  have hbarrier : diagonalBarrier (horizontalMirror U) = fun x => diagonalBarrier U (-x) :=
    funext (diagonalBarrier_horizontalMirror U)
  rw [hroof, hbarrier, intervalSpatialScore_reflect]

theorem diagonalComparisonScore_horizontalTranslate {U : Set Plane}
    (hU : IsDownwardCap U) (d : ℝ) :
    diagonalComparisonScore (horizontalTranslate U d) = diagonalComparisonScore U := by
  unfold diagonalComparisonScore
  rw [horizontalLeft_horizontalTranslate hU, horizontalRight_horizontalTranslate hU]
  have hroof : capRoof (horizontalTranslate U d) = fun x => capRoof U (x - d) :=
    funext (capRoof_horizontalTranslate U d)
  have hbarrier : diagonalBarrier (horizontalTranslate U d) = fun x => diagonalBarrier U (x - d) := by
    funext x
    rw [diagonalBarrier, cornerWall_horizontalTranslate hU]
    rfl
  rw [hroof, hbarrier, intervalSpatialScore_translate]

theorem diagonalComparisonScore_centeredCap {U : Set Plane} (hU : IsDownwardCap U) :
    diagonalComparisonScore (centeredCap U) = diagonalComparisonScore U :=
  diagonalComparisonScore_horizontalTranslate hU _

theorem diagonalComparisonScore_centered_quarters {U : Set Plane} {C : ℝ}
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C) :
    diagonalComparisonScore U = (∫ x in (-2 * C)..(-C), capRoof U x) +
      (∫ x in C..(2 * C), capRoof U x) - ∫ x in (-C)..C, diagonalBarrier U x := by
  rw [diagonalComparisonScore, hleft, hright, intervalSpatialScore,
    show -2 * C + (2 * C - -2 * C) / 4 = -C by ring,
    show 2 * C - (2 * C - -2 * C) / 4 = C by ring]

end AmbidextrousSofa
