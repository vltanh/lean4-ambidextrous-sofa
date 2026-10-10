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

theorem divisions_pos (n : ℕ) : 0 < divisions n := by
  unfold divisions
  positivity

theorem divisions_ge_two (n : ℕ) : 2 ≤ divisions n := by
  calc
    2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

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
  constructor
  · intro ht
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
    exact ⟨i.val, Nat.lt_succ_iff.mp i.isLt, rfl⟩
  · rintro ⟨i, hi, ht⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨i, Nat.lt_succ_iff.mpr hi⟩, Finset.mem_univ _, ?_⟩
    exact Subtype.ext ht.symm

theorem dyadic_mono : Monotone dyadic := by
  intro n m hnm t ht
  obtain ⟨i, hi, ht⟩ := (mem_dyadic_iff n t).mp ht
  have hfactor : divisions m = divisions n * 2 ^ (m - n) := by
    unfold divisions
    rw [← pow_add]
    congr 1
    omega
  apply (mem_dyadic_iff m t).mpr
  refine ⟨i * 2 ^ (m - n), ?_, ?_⟩
  · rw [hfactor]
    exact Nat.mul_le_mul_right _ hi
  · rw [ht, hfactor]
    push_cast
    have hp : (2 : ℝ) ^ (m - n) ≠ 0 := by positivity
    have hN : (divisions n : ℝ) ≠ 0 := by exact_mod_cast (divisions_pos n).ne'
    field_simp <;> ring

/-- The floor of the rescaled angle is a grid point at distance less than
one mesh. Closed endpoints require no separate positive-distance case. -/
theorem exists_dyadic_near (t : QuarterAngle) {ε : ℝ} (hε : 0 < ε) :
    ∃ n, ∃ s ∈ dyadic n, dist s t < ε := by
  have hL : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
  obtain ⟨n, hn⟩ := exists_nat_gt ((Real.pi / 2) / ε)
  have hnN : (n : ℝ) < divisions n := by
    have h : n < divisions n :=
      lt_trans (Nat.lt_succ_self n) (show n + 1 < 2 ^ (n + 1) from Nat.lt_two_pow_self)
    exact_mod_cast h
  have hN : (0 : ℝ) < divisions n := by exact_mod_cast divisions_pos n
  let z : ℝ := (t : ℝ) * divisions n / (Real.pi / 2)
  have hz0 : 0 ≤ z := div_nonneg (mul_nonneg t.property.1 hN.le) hL.le
  have hzN : z ≤ divisions n := by
    change (t : ℝ) * divisions n / (Real.pi / 2) ≤ divisions n
    rw [div_le_iff₀ hL]
    nlinarith [t.property.2]
  let j : ℕ := ⌊z⌋₊
  have hjle : (j : ℝ) ≤ z := Nat.floor_le hz0
  have hjgt : z < (j : ℝ) + 1 := Nat.lt_floor_add_one z
  have hjN : j ≤ divisions n := by exact_mod_cast hjle.trans hzN
  let s : QuarterAngle := dyadicPoint n ⟨j, Nat.lt_succ_iff.mpr hjN⟩
  have hs : s ∈ dyadic n := (mem_dyadic_iff n s).mpr ⟨j, hjN, rfl⟩
  have hleft : (j : ℝ) * (Real.pi / 2) ≤ (t : ℝ) * divisions n := by
    have h := hjle
    change (j : ℝ) ≤ (t : ℝ) * divisions n / (Real.pi / 2) at h
    exact (le_div_iff₀ hL).mp h
  have hright : (t : ℝ) * divisions n < ((j : ℝ) + 1) * (Real.pi / 2) := by
    have h := hjgt
    change (t : ℝ) * divisions n / (Real.pi / 2) < (j : ℝ) + 1 at h
    exact (div_lt_iff₀ hL).mp h
  have hsle : (j : ℝ) * (Real.pi / 2) / divisions n ≤ (t : ℝ) :=
    (div_le_iff₀ hN).mpr hleft
  have hgap : (t : ℝ) - (j : ℝ) * (Real.pi / 2) / divisions n <
      (Real.pi / 2) / divisions n := by
    rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hN]
    nlinarith
  have hmesh : (Real.pi / 2) / divisions n < ε := by
    rw [div_lt_iff₀ hN]
    have hratio := hn.trans hnN
    rw [div_lt_iff₀ hε] at hratio
    nlinarith
  refine ⟨n, s, hs, ?_⟩
  change dist ((j : ℝ) * (Real.pi / 2) / divisions n) (t : ℝ) < ε
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hsle)]
  exact hgap.trans hmesh

theorem dense_iUnion_dyadic : Dense (⋃ n, (dyadic n : Set QuarterAngle)) := by
  apply Metric.dense_iff.mpr
  intro t ε hε
  obtain ⟨n, s, hs, hdist⟩ := exists_dyadic_near t hε
  exact ⟨s, hdist, mem_iUnion.mpr ⟨n, hs⟩⟩

theorem tendstoUniformlyOn_dyadic_box {B : Set Plane} (hB : IsCompact B) (l r : ℝ) :
    TendstoUniformlyOn (fun n (p : CompactCap × ℝ) => niche p.1 (dyadic n) p.2)
      (fun p => sweptNiche p.1.carrier (Real.pi / 2) p.2)
      atTop (boxedCaps B ×ˢ Icc l r) :=
  tendstoUniformlyOn_niche_box dyadic dyadic_mono dense_iUnion_dyadic hB l r

end AngularGrid

end AmbidextrousSofa
