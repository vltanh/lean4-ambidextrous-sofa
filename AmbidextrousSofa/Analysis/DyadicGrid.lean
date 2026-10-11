module

public import AmbidextrousSofa.Analysis.GridNiche

@[expose] public section

/-!
# Concrete nested equally spaced quarter-angle grids

Stage `n` has `2^(n+1)` equal intervals. Its closed grid contains both zero
clipped endpoint values. The floor construction proves dense union directly,
so the uniform niche approximation theorem applies to these actual grids.
Only the open grid points supply polygon support walls.
-/

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology

namespace AmbidextrousSofa

namespace AngularGrid

def divisions (n : ℕ) : ℕ := 2 ^ (n + 1)

theorem divisions_pos (n : ℕ) : 0 < divisions n := pow_pos two_pos _

theorem divisions_ge_two (n : ℕ) : 2 ≤ divisions n := Nat.le_self_pow n.succ_ne_zero 2

def dyadicPoint (n : ℕ) (i : Fin (divisions n + 1)) : QuarterAngle :=
  ⟨(i.val : ℝ) * (Real.pi / 2) / divisions n, by
    have hN : (0 : ℝ) < divisions n := by exact_mod_cast divisions_pos n
    have hi : (i.val : ℝ) ≤ divisions n := by
      exact_mod_cast Nat.lt_succ_iff.mp i.isLt
    have hL : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
    constructor
    · positivity
    · rw [div_le_iff₀ hN]
      nlinarith⟩

def dyadic (n : ℕ) : Finset QuarterAngle := by
  classical
  exact Finset.univ.image (dyadicPoint n)

theorem mem_dyadic_iff (n : ℕ) (t : QuarterAngle) :
    t ∈ dyadic n ↔ ∃ i : ℕ, i ≤ divisions n ∧
      (t : ℝ) = (i : ℝ) * (Real.pi / 2) / divisions n := by
  classical
  refine ⟨fun ht => ?_, fun ⟨i, hi, ht⟩ => Finset.mem_image.mpr
    ⟨⟨i, Nat.lt_succ_iff.mpr hi⟩, Finset.mem_univ _, Subtype.ext ht.symm⟩⟩
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
  exact ⟨i.val, Nat.lt_succ_iff.mp i.isLt, rfl⟩

theorem dyadic_mono : Monotone dyadic := by
  intro n m hnm t ht
  obtain ⟨i, hi, ht⟩ := (mem_dyadic_iff n t).mp ht
  have hfactor : divisions m = divisions n * 2 ^ (m - n) := by
    rw [divisions, divisions, ← pow_add]
    congr 1
    omega
  refine (mem_dyadic_iff m t).mpr ⟨i * 2 ^ (m - n), hfactor ▸ Nat.mul_le_mul_right _ hi, ?_⟩
  rw [ht, hfactor]
  have hN : (divisions n : ℝ) ≠ 0 := by exact_mod_cast (divisions_pos n).ne'
  push_cast
  field_simp

theorem dense_iUnion_dyadic : Dense (⋃ n, (dyadic n : Set QuarterAngle)) := by
  -- The floor of the rescaled angle is a grid point less than one mesh below `t`.
  refine Metric.dense_iff.mpr fun t ε hε => ?_
  obtain ⟨n, hn⟩ := exists_nat_gt ((Real.pi / 2) / ε)
  have hnN : (n : ℝ) < divisions n := by
    exact_mod_cast (Nat.lt_succ_self n).trans Nat.lt_two_pow_self
  have hN : (0 : ℝ) < divisions n := by exact_mod_cast divisions_pos n
  set z := (t : ℝ) * divisions n / (Real.pi / 2) with hz
  have hz0 : 0 ≤ z := div_nonneg (mul_nonneg t.property.1 hN.le) (by positivity)
  have hjN : ⌊z⌋₊ ≤ divisions n := Nat.floor_le_of_le <| by
    rw [hz, div_le_iff₀ (by positivity)]
    nlinarith [t.property.2]
  have hmesh : 0 < (Real.pi / 2) / divisions n := by positivity
  have hmeshε : (Real.pi / 2) / divisions n < ε := by
    rw [div_lt_iff₀ hN]
    rw [div_lt_iff₀ hε] at hn
    nlinarith
  have hts : (t : ℝ) - ⌊z⌋₊ * (Real.pi / 2) / divisions n =
      (z - ⌊z⌋₊) * ((Real.pi / 2) / divisions n) := by
    rw [hz]
    field_simp
  refine ⟨dyadicPoint n ⟨⌊z⌋₊, Nat.lt_succ_iff.mpr hjN⟩, ?_,
    mem_iUnion.mpr ⟨n, (mem_dyadic_iff n _).mpr ⟨_, hjN, rfl⟩⟩⟩
  rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_sub_comm, abs_lt]
  change -ε < (t : ℝ) - ⌊z⌋₊ * (Real.pi / 2) / divisions n ∧
    (t : ℝ) - ⌊z⌋₊ * (Real.pi / 2) / divisions n < ε
  rw [hts]
  constructor <;> linarith [mul_nonneg (sub_nonneg.mpr (Nat.floor_le hz0)) hmesh.le,
    mul_lt_mul_of_pos_right (by linarith [Nat.lt_floor_add_one z] : z - ⌊z⌋₊ < 1) hmesh]

theorem tendstoUniformlyOn_dyadic_box {B : Set Plane} (hB : IsCompact B) (l r : ℝ) :
    TendstoUniformlyOn (fun n (p : CompactCap × ℝ) => niche p.1 (dyadic n) p.2)
      (fun p => sweptNiche p.1.carrier (Real.pi / 2) p.2)
      atTop (boxedCaps B ×ˢ Icc l r) :=
  tendstoUniformlyOn_niche_box dyadic dyadic_mono dense_iUnion_dyadic hB l r

end AngularGrid

end AmbidextrousSofa
