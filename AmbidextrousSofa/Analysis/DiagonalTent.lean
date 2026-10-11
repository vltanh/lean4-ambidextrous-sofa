module

public import AmbidextrousSofa.Analysis.PositiveTent
public import AmbidextrousSofa.Analysis.WideCap

@[expose] public section

/-!
# The genuine diagonal two-ray tent

At the exact angle pi/4 the two inner walls use the actual support maxima
of x+y and -x+y. Their minimum is a tent. Clipping its negative part gives
the diagonal barrier, a pointwise lower bound for every full or partial
barrier whose visited range reaches pi/4, including the terminal endpoint case.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def diagonalRight (U : Set Plane) : ℝ := support U (1, 1)

def diagonalLeft (U : Set Plane) : ℝ := support U (-1, 1)

/-- The positive part of the corner at `π / 4`. -/
def diagonalBarrier (U : Set Plane) (x : ℝ) : ℝ :=
  max (cornerWall U (Real.pi / 4) x) 0

theorem firstWall_pi_div_four_eq_diagonal {U : Set Plane}
    (hU : IsDownwardCap U) (x : ℝ) :
    firstWall U (Real.pi / 4) x = diagonalRight U - Real.sqrt 2 - x := by
  have hn : unitNormal (Real.pi / 4) = (Real.sqrt 2 / 2) • (1, 1) := by
    apply Prod.ext <;> simp [unitNormal, Real.cos_pi_div_four, Real.sin_pi_div_four]
  rw [firstWall, hn, support_smul_direction hU.isCompact hU.nonempty _ (by positivity),
    Real.sin_pi_div_four, Real.cos_pi_div_four, div_eq_iff (by positivity), diagonalRight]
  linarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem secondWall_pi_div_four_eq_diagonal {U : Set Plane}
    (hU : IsDownwardCap U) (x : ℝ) :
    secondWall U (Real.pi / 4) x = diagonalLeft U - Real.sqrt 2 + x := by
  have hn : companionNormal (Real.pi / 4) = (Real.sqrt 2 / 2) • (-1, 1) := by
    apply Prod.ext <;> simp [companionNormal, Real.cos_pi_div_four, Real.sin_pi_div_four]
  rw [secondWall, hn, support_smul_direction hU.isCompact hU.nonempty _ (by positivity),
    Real.sin_pi_div_four, Real.cos_pi_div_four, div_eq_iff (by positivity), diagonalLeft]
  linarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem diagonalBarrier_nonneg (U : Set Plane) (x : ℝ) : 0 ≤ diagonalBarrier U x :=
  le_max_right _ _

theorem continuous_diagonalBarrier (U : Set Plane) : Continuous (diagonalBarrier U) := by
  unfold diagonalBarrier cornerWall firstWall secondWall
  fun_prop

theorem IsDownwardCap.diagonalBarrier_eq_tent {U : Set Plane} (hU : IsDownwardCap U) (x : ℝ) :
    diagonalBarrier U x = max ((diagonalRight U + diagonalLeft U) / 2 - Real.sqrt 2 -
      |x - (diagonalRight U - diagonalLeft U) / 2|) 0 := by
  rw [diagonalBarrier, cornerWall, firstWall_pi_div_four_eq_diagonal hU,
    secondWall_pi_div_four_eq_diagonal hU, ← min_symmetric_lines]
  ring_nf

theorem IsDownwardCap.diagonalBarrier_le_partialBarrier {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα0 : Real.pi / 4 ≤ α)
    (hαL : α ≤ Real.pi / 2) (x : ℝ) : diagonalBarrier U x ≤ partialBarrier U α x :=
  max_le (cornerWall_pi_div_four_le_partialBarrier hU.isCompact hα0 hαL x)
    (partialBarrier_nonneg _ _ _)

theorem IsDownwardCap.diagonalRight_ge {U : Set Plane} (hU : IsDownwardCap U)
    {p : Plane} (hp : p ∈ U) : p.1 + p.2 ≤ diagonalRight U := by
  simpa only [diagonalRight, coordDot, mul_one] using coordDot_le_support hU.isCompact hp (1, 1)

theorem IsDownwardCap.diagonalLeft_ge {U : Set Plane} (hU : IsDownwardCap U)
    {p : Plane} (hp : p ∈ U) : -p.1 + p.2 ≤ diagonalLeft U := by
  simpa only [diagonalLeft, coordDot, mul_neg_one, mul_one] using
    coordDot_le_support hU.isCompact hp (-1, 1)

theorem IsDownwardCap.capRoof_le_diagonalRight {U : Set Plane} (hU : IsDownwardCap U)
    {x : ℝ} (hx : x ∈ horizontalProjection U) : capRoof U x ≤ diagonalRight U - x := by
  linarith [hU.diagonalRight_ge (capRoof_mem hU.isCompact hx)]

theorem IsDownwardCap.capRoof_le_diagonalLeft {U : Set Plane} (hU : IsDownwardCap U)
    {x : ℝ} (hx : x ∈ horizontalProjection U) : capRoof U x ≤ diagonalLeft U + x := by
  linarith [hU.diagonalLeft_ge (capRoof_mem hU.isCompact hx)]

theorem IsDownwardCap.diagonalRight_le {U : Set Plane} (hU : IsDownwardCap U) :
    diagonalRight U ≤ horizontalRight U + 1 :=
  support_le_of_forall hU.nonempty fun p hp => by
    have : p.1 ≤ horizontalRight U :=
      le_csSup (isCompact_horizontalProjection hU.isCompact).bddAbove ⟨p, hp, rfl⟩
    simp only [coordDot, mul_one]
    linarith [(hU.inStrip hp).2]

theorem IsDownwardCap.diagonalLeft_le {U : Set Plane} (hU : IsDownwardCap U) :
    diagonalLeft U ≤ -horizontalLeft U + 1 :=
  support_le_of_forall hU.nonempty fun p hp => by
    have : horizontalLeft U ≤ p.1 :=
      csInf_le (isCompact_horizontalProjection hU.isCompact).bddBelow ⟨p, hp, rfl⟩
    simp only [coordDot, mul_neg_one, mul_one]
    linarith [(hU.inStrip hp).2]

end AmbidextrousSofa
