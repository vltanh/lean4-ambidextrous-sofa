module

public import AmbidextrousSofa.Analysis.NearDiagonalGeometry
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

@[expose] public section

/-!
# Actual two-wall competitors at a pair of near-diagonal angles

The angles are `arctan k` and its quarter-turn complement. Their unit
normals are positive multiples of the four unnormalized directions used
in the actual support-deficit calculation. Every displayed wall bound
therefore comes from an actual support of the original cap.

For `k = √2 - 1` the two corners and the diagonal corner form the
three-angle barrier. Every barrier whose visited range reaches
`π / 2 - arctan k` lies above it, so its spatial score bounds the cap score.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def nearDiagonalNorm (k : ℝ) : ℝ := Real.sqrt (1 + k ^ 2)

theorem nearDiagonalNorm_pos (k : ℝ) : 0 < nearDiagonalNorm k := Real.sqrt_pos.mpr (by positivity)

theorem nearDiagonalNorm_sq (k : ℝ) : nearDiagonalNorm k ^ 2 = 1 + k ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem IsDownwardCap.support_div {U : Set Plane} (hU : IsDownwardCap U) (p q : ℝ) {c : ℝ}
    (hc : 0 ≤ c) : support U (p / c, q / c) = support U (p, q) / c := by
  simpa [div_eq_inv_mul] using
    support_smul_direction hU.isCompact hU.nonempty (p, q) (inv_nonneg.mpr hc)

theorem IsDownwardCap.firstWall_arctan {U : Set Plane} (hU : IsDownwardCap U)
    {k : ℝ} (hk : k ≠ 0) (x : ℝ) :
    firstWall U (Real.arctan k) x = (support U (1, k) - nearDiagonalNorm k - x) / k := by
  rw [firstWall, unitNormal, Real.cos_arctan, Real.sin_arctan,
    hU.support_div _ _ (by positivity), nearDiagonalNorm]
  field_simp

theorem IsDownwardCap.secondWall_arctan {U : Set Plane} (hU : IsDownwardCap U)
    (k x : ℝ) :
    secondWall U (Real.arctan k) x = support U (-k, 1) - nearDiagonalNorm k + k * x := by
  rw [secondWall, companionNormal, Real.cos_arctan, Real.sin_arctan, ← neg_div,
    hU.support_div _ _ (by positivity), nearDiagonalNorm]
  field_simp

theorem IsDownwardCap.firstWall_complement_arctan {U : Set Plane} (hU : IsDownwardCap U)
    (k x : ℝ) : firstWall U (Real.pi / 2 - Real.arctan k) x =
      support U (k, 1) - nearDiagonalNorm k - k * x := by
  rw [firstWall, unitNormal, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, Real.cos_arctan,
    Real.sin_arctan, hU.support_div _ _ (by positivity), nearDiagonalNorm]
  field_simp

theorem IsDownwardCap.secondWall_complement_arctan {U : Set Plane} (hU : IsDownwardCap U)
    {k : ℝ} (hk : k ≠ 0) (x : ℝ) :
    secondWall U (Real.pi / 2 - Real.arctan k) x =
      (support U (-1, k) - nearDiagonalNorm k + x) / k := by
  rw [secondWall, companionNormal, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub,
    Real.cos_arctan, Real.sin_arctan, ← neg_div, hU.support_div _ _ (by positivity),
    nearDiagonalNorm]
  field_simp

theorem arctan_le_complement_arctan {k : ℝ} (hk : k ≤ 1) :
    Real.arctan k ≤ Real.pi / 2 - Real.arctan k := by
  linarith [Real.arctan_one ▸ Real.arctan_strictMono.monotone hk]

/-- The barrier of the three corners at `π / 4`, `arctan k` and `π / 2 - arctan k`, for
`k = √2 - 1`. -/
def threeAngleBarrier (U : Set Plane) (x : ℝ) : ℝ :=
  max (diagonalBarrier U x)
    (max (cornerWall U (Real.arctan (Real.sqrt 2 - 1)) x)
      (cornerWall U (Real.pi / 2 - Real.arctan (Real.sqrt 2 - 1)) x))

theorem continuous_threeAngleBarrier (U : Set Plane) : Continuous (threeAngleBarrier U) := by
  unfold threeAngleBarrier diagonalBarrier cornerWall firstWall secondWall
  fun_prop

/-- Lower bounds `A` and `B` for the two supports at the angle `arctan k`, `k = √2 - 1`, bound
the three-angle barrier from below. -/
theorem IsDownwardCap.threeAngleBarrier_ge_first {U : Set Plane} (hU : IsDownwardCap U)
    {k A B : ℝ} (hk : k = Real.sqrt 2 - 1) (hA : A ≤ support U (1, k))
    (hB : B ≤ support U (-k, 1)) (x : ℝ) :
    min ((A - nearDiagonalNorm k - x) / k) (B - nearDiagonalNorm k + k * x) ≤
      threeAngleBarrier U x := by
  subst hk
  have hk0 : 0 < Real.sqrt 2 - 1 := by linarith [sqrt_two_sub_one_strict_bounds.1]
  refine le_trans ?_ ((le_max_left _ _).trans (le_max_right _ _))
  rw [cornerWall, hU.firstWall_arctan hk0.ne', hU.secondWall_arctan]
  exact min_le_min (div_le_div_of_nonneg_right (by linarith) hk0.le) (by linarith)

/-- The same at the complementary angle `π / 2 - arctan k`. -/
theorem IsDownwardCap.threeAngleBarrier_ge_last {U : Set Plane} (hU : IsDownwardCap U)
    {k A B : ℝ} (hk : k = Real.sqrt 2 - 1) (hA : A ≤ support U (k, 1))
    (hB : B ≤ support U (-1, k)) (x : ℝ) :
    min (A - nearDiagonalNorm k - k * x) ((B - nearDiagonalNorm k + x) / k) ≤
      threeAngleBarrier U x := by
  subst hk
  have hk0 : 0 < Real.sqrt 2 - 1 := by linarith [sqrt_two_sub_one_strict_bounds.1]
  refine le_trans ?_ ((le_max_right _ _).trans (le_max_right _ _))
  rw [cornerWall, hU.firstWall_complement_arctan, hU.secondWall_complement_arctan hk0.ne']
  exact min_le_min (by linarith) (div_le_div_of_nonneg_right (by linarith) hk0.le)

theorem IsDownwardCap.threeAngleBarrier_le_partialBarrier {U : Set Plane} (hU : IsDownwardCap U)
    {α : ℝ} (hnear : Real.pi / 2 - Real.arctan (Real.sqrt 2 - 1) ≤ α)
    (hαL : α ≤ Real.pi / 2) (x : ℝ) : threeAngleBarrier U x ≤ partialBarrier U α x := by
  have hk := sqrt_two_sub_one_strict_bounds
  have hc := arctan_le_complement_arctan (k := Real.sqrt 2 - 1) (by linarith only [hk.2.2])
  exact max_le (hU.diagonalBarrier_le_partialBarrier (by linarith only [hc, hnear]) hαL x)
    (max_le (cornerWall_le_partialBarrier hU.isCompact
      (Real.arctan_pos.mpr (by linarith only [hk.1])) (hc.trans hnear) hαL x)
      (cornerWall_le_partialBarrier hU.isCompact (sub_pos.mpr (Real.arctan_lt_pi_div_two _))
        hnear hαL x))

/-- The cap score at every terminal angle reaching `π / 2 - arctan k` is at most the spatial
score of the three-angle barrier. -/
theorem IsDownwardCap.capScore_le_threeAngleScore {U : Set Plane} (hU : IsDownwardCap U)
    {α : ℝ} (hnear : Real.pi / 2 - Real.arctan (Real.sqrt 2 - 1) ≤ α) (hαL : α ≤ Real.pi / 2) :
    capScore U α ≤ intervalSpatialScore (capRoof U) (threeAngleBarrier U)
      (horizontalLeft U) (horizontalRight U) := by
  rw [hU.capScore_eq_intervalSpatialScore]
  refine sub_le_sub_left (intervalIntegral.integral_mono_on ?_
    ((continuous_threeAngleBarrier U).intervalIntegrable _ _)
    (hU.intervalIntegrable_partialBarrier ((sub_pos.mpr (Real.arctan_lt_pi_div_two _)).trans_le
      hnear) hαL _ _) fun x _ => hU.threeAngleBarrier_le_partialBarrier hnear hαL x) _
  linarith only [horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact]

end AmbidextrousSofa
