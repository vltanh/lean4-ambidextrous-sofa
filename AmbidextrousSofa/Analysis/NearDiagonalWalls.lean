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
-/

noncomputable section

open Set

namespace AmbidextrousSofa

def nearDiagonalNorm (k : ℝ) : ℝ := Real.sqrt (1 + k ^ 2)

theorem nearDiagonalNorm_pos (k : ℝ) : 0 < nearDiagonalNorm k := by
  unfold nearDiagonalNorm
  positivity

theorem nearDiagonalNorm_sq (k : ℝ) : nearDiagonalNorm k ^ 2 = 1 + k ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem unitNormal_arctan (k : ℝ) :
    unitNormal (Real.arctan k) = (1 / nearDiagonalNorm k) • (1, k) := by
  apply Prod.ext <;> simp [unitNormal, Real.sin_arctan, Real.cos_arctan,
    nearDiagonalNorm, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem companionNormal_arctan (k : ℝ) :
    companionNormal (Real.arctan k) = (1 / nearDiagonalNorm k) • (-k, 1) := by
  apply Prod.ext <;> simp [companionNormal, Real.sin_arctan, Real.cos_arctan,
    nearDiagonalNorm, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem unitNormal_complement_arctan (k : ℝ) :
    unitNormal (Real.pi / 2 - Real.arctan k) = (1 / nearDiagonalNorm k) • (k, 1) := by
  rw [unitNormal, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  apply Prod.ext <;> simp [Real.sin_arctan, Real.cos_arctan, nearDiagonalNorm, smul_eq_mul,
    div_eq_mul_inv, mul_comm]

theorem companionNormal_complement_arctan (k : ℝ) :
    companionNormal (Real.pi / 2 - Real.arctan k) = (1 / nearDiagonalNorm k) • (-1, k) := by
  rw [companionNormal, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  apply Prod.ext <;> simp [Real.sin_arctan, Real.cos_arctan, nearDiagonalNorm, smul_eq_mul,
    div_eq_mul_inv, mul_comm]

theorem IsDownwardCap.firstWall_arctan {U : Set Plane} (hU : IsDownwardCap U)
    {k : ℝ} (hk : k ≠ 0) (x : ℝ) :
    firstWall U (Real.arctan k) x = (support U (1, k) - nearDiagonalNorm k - x) / k := by
  have hb := nearDiagonalNorm_pos k
  rw [firstWall, unitNormal_arctan,
    support_smul_direction hU.isCompact hU.nonempty _ (by positivity),
    Real.cos_arctan, Real.sin_arctan]
  change ((1 / nearDiagonalNorm k) * support U (1, k) - 1 - x * (1 / nearDiagonalNorm k)) /
      (k / nearDiagonalNorm k) = _
  field_simp [hk, hb.ne'] <;> ring

theorem IsDownwardCap.secondWall_arctan {U : Set Plane} (hU : IsDownwardCap U)
    (k x : ℝ) :
    secondWall U (Real.arctan k) x = support U (-k, 1) - nearDiagonalNorm k + k * x := by
  have hb := nearDiagonalNorm_pos k
  rw [secondWall, companionNormal_arctan,
    support_smul_direction hU.isCompact hU.nonempty _ (by positivity),
    Real.cos_arctan, Real.sin_arctan]
  change ((1 / nearDiagonalNorm k) * support U (-k, 1) - 1 + x * (k / nearDiagonalNorm k)) /
      (1 / nearDiagonalNorm k) = _
  field_simp [hb.ne'] <;> ring

theorem IsDownwardCap.firstWall_complement_arctan {U : Set Plane} (hU : IsDownwardCap U)
    (k x : ℝ) : firstWall U (Real.pi / 2 - Real.arctan k) x =
      support U (k, 1) - nearDiagonalNorm k - k * x := by
  have hb := nearDiagonalNorm_pos k
  rw [firstWall, unitNormal_complement_arctan,
    support_smul_direction hU.isCompact hU.nonempty _ (by positivity),
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, Real.cos_arctan, Real.sin_arctan]
  change ((1 / nearDiagonalNorm k) * support U (k, 1) - 1 - x * (k / nearDiagonalNorm k)) /
      (1 / nearDiagonalNorm k) = _
  field_simp [hb.ne'] <;> ring

theorem IsDownwardCap.secondWall_complement_arctan {U : Set Plane} (hU : IsDownwardCap U)
    {k : ℝ} (hk : k ≠ 0) (x : ℝ) :
    secondWall U (Real.pi / 2 - Real.arctan k) x =
      (support U (-1, k) - nearDiagonalNorm k + x) / k := by
  have hb := nearDiagonalNorm_pos k
  rw [secondWall, companionNormal_complement_arctan,
    support_smul_direction hU.isCompact hU.nonempty _ (by positivity),
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, Real.cos_arctan, Real.sin_arctan]
  change ((1 / nearDiagonalNorm k) * support U (-1, k) - 1 + x * (1 / nearDiagonalNorm k)) /
      (k / nearDiagonalNorm k) = _
  field_simp [hk, hb.ne'] <;> ring

theorem IsDownwardCap.cornerWall_le_partialBarrier_of_angle_le {U : Set Plane}
    (hU : IsDownwardCap U) {t α : ℝ} (ht0 : 0 < t) (htα : t ≤ α)
    (hαL : α ≤ Real.pi / 2) (x : ℝ) : cornerWall U t x ≤ partialBarrier U α x := by
  rcases lt_or_eq_of_le htα with hlt | heq
  · exact (cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCompact hαL x)
      ⟨ht0, hlt⟩).trans (le_max_left _ _)
  · subst t
    exact (min_le_left _ _).trans (le_max_right _ _)

theorem arctan_le_complement_arctan {k : ℝ} (hk : k ≤ 1) :
    Real.arctan k ≤ Real.pi / 2 - Real.arctan k := by
  have h := Real.arctan_strictMono.monotone hk
  rw [Real.arctan_one] at h
  linarith

/-- The lower two-wall competitor uses the actual left near-vertical
support and an actual point attaining the right diagonal support. -/
theorem IsDownwardCap.nearDiagonal_left_competitor_le {U : Set Plane}
    (hU : IsDownwardCap U) {h k u v α : ℝ} (hk : 0 < k) (hk1 : k ≤ 1)
    (hα0 : Real.pi / 2 - Real.arctan k ≤ α) (hαL : α ≤ Real.pi / 2)
    (hcomp : u + k ≤ support U (1, k)) (x : ℝ) :
    min ((u + k - nearDiagonalNorm k - x) / k)
      (1 - h + k * v - nearDiagonalLeftDeficit U h k v - nearDiagonalNorm k + k * x) ≤
        partialBarrier U α x := by
  apply le_trans _ (hU.cornerWall_le_partialBarrier_of_angle_le
    (Real.arctan_pos.mpr hk) ((arctan_le_complement_arctan hk1).trans hα0) hαL x)
  rw [cornerWall, hU.firstWall_arctan hk.ne', hU.secondWall_arctan]
  apply min_le_min
  · exact div_le_div_of_nonneg_right (by linarith) hk.le
  · unfold nearDiagonalLeftDeficit
    linarith

/-- The reflected competitor retains the lower actual companion height. -/
theorem IsDownwardCap.nearDiagonal_right_competitor_le {U : Set Plane}
    (hU : IsDownwardCap U) {h k u v α : ℝ} (hk : 0 < k)
    (hα0 : Real.pi / 2 - Real.arctan k ≤ α) (hαL : α ≤ Real.pi / 2)
    (hcomp : v + k * (1 - h) ≤ support U (-1, k)) (x : ℝ) :
    min ((v + k * (1 - h) - nearDiagonalNorm k + x) / k)
      (1 + k * u - nearDiagonalRightDeficit U k u - nearDiagonalNorm k - k * x) ≤
        partialBarrier U α x := by
  apply le_trans _ (hU.cornerWall_le_partialBarrier_of_angle_le
    (sub_pos.mpr (Real.arctan_lt_pi_div_two k)) hα0 hαL x)
  rw [cornerWall, hU.firstWall_complement_arctan, hU.secondWall_complement_arctan hk.ne',
    min_comm (support U (k, 1) - nearDiagonalNorm k - k * x)]
  apply min_le_min
  · exact div_le_div_of_nonneg_right (by linarith) hk.le
  · unfold nearDiagonalRightDeficit
    linarith

end AmbidextrousSofa
