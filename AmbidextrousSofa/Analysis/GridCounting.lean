import AmbidextrousSofa.Analysis.DyadicNeighbors

/-!
# Counting actual dyadic source angles

The open upper source normals have distinct positive integer mesh
indices. Their distances from the other horizontal axis have the same
property. Consequently a prefix of angular length `ε` contains at most
`ε / mesh` sources, with no loss depending on a rounded endpoint.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

namespace AngularGrid

theorem divisions_mul_mesh (n : ℕ) : (divisions n : ℝ) * mesh n = Real.pi / 2 := by
  have hN : (divisions n : ℝ) ≠ 0 := by exact_mod_cast (divisions_pos n).ne'
  unfold mesh
  field_simp [hN]

theorem interior_dyadic_index (n : ℕ) (t : InteriorPoint (dyadic n)) :
    ∃ i : ℕ, 0 < i ∧ i < divisions n ∧ (t.val : ℝ) = (i : ℝ) * mesh n := by
  obtain ⟨i, hi, hti⟩ := (mem_dyadic_iff n t.val).mp (interiorPoint_mem_grid _ t)
  have ht := interiorPoint_mem (dyadic n) t
  have hi0 : 0 < i := by
    by_contra h
    have hi' : i = 0 := by omega
    rw [hi'] at hti
    simp only [Nat.cast_zero, zero_mul, zero_div] at hti
    linarith [ht.1]
  have hiN : i < divisions n := by
    by_contra h
    have hi' : i = divisions n := by omega
    rw [hi'] at hti
    have heq : (t.val : ℝ) = Real.pi / 2 := by
      calc
        (t.val : ℝ) = (divisions n : ℝ) * mesh n := by rw [hti, mesh]; ring
        _ = _ := divisions_mul_mesh n
    linarith [ht.2]
  refine ⟨i, hi0, hiN, ?_⟩
  rw [hti, mesh]
  ring

theorem fullAngle_integer_mesh (n : ℕ) (j : SourceIndex (dyadic n)) :
    ∃ i : ℕ, 0 < i ∧ i < 2 * divisions n ∧
      fullAngle (dyadic n) j = (i : ℝ) * mesh n := by
  cases j with
  | inl t =>
    obtain ⟨i, hi0, hiN, ht⟩ := interior_dyadic_index n t
    exact ⟨i, hi0, by omega, ht⟩
  | inr t =>
    obtain ⟨i, hi0, hiN, ht⟩ := interior_dyadic_index n t
    refine ⟨i + divisions n, by omega, by omega, ?_⟩
    change (t.val : ℝ) + Real.pi / 2 = ((i + divisions n : ℕ) : ℝ) * mesh n
    rw [ht, Nat.cast_add, add_mul, divisions_mul_mesh]

def fullGridIndex (n : ℕ) (j : SourceIndex (dyadic n)) : ℕ :=
  (fullAngle_integer_mesh n j).choose

theorem fullGridIndex_pos (n : ℕ) (j : SourceIndex (dyadic n)) : 0 < fullGridIndex n j :=
  (fullAngle_integer_mesh n j).choose_spec.1

theorem fullGridIndex_lt (n : ℕ) (j : SourceIndex (dyadic n)) :
    fullGridIndex n j < 2 * divisions n :=
  (fullAngle_integer_mesh n j).choose_spec.2.1

theorem fullAngle_eq_index_mul_mesh (n : ℕ) (j : SourceIndex (dyadic n)) :
    fullAngle (dyadic n) j = (fullGridIndex n j : ℝ) * mesh n :=
  (fullAngle_integer_mesh n j).choose_spec.2.2

theorem fullGridIndex_injective (n : ℕ) : Function.Injective (fullGridIndex n) := by
  intro i j hij
  apply fullAngle_injective (dyadic n)
  rw [fullAngle_eq_index_mul_mesh, fullAngle_eq_index_mul_mesh, hij]

def reverseGridIndex (n : ℕ) (j : SourceIndex (dyadic n)) : ℕ :=
  2 * divisions n - fullGridIndex n j

theorem reverseGridIndex_pos (n : ℕ) (j : SourceIndex (dyadic n)) :
    0 < reverseGridIndex n j := by
  unfold reverseGridIndex
  exact Nat.sub_pos_of_lt (fullGridIndex_lt n j)

theorem pi_sub_fullAngle_eq_index_mul_mesh (n : ℕ) (j : SourceIndex (dyadic n)) :
    Real.pi - fullAngle (dyadic n) j = (reverseGridIndex n j : ℝ) * mesh n := by
  rw [fullAngle_eq_index_mul_mesh, reverseGridIndex,
    Nat.cast_sub (fullGridIndex_lt n j).le, Nat.cast_mul, Nat.cast_ofNat]
  have h := divisions_mul_mesh n
  nlinarith

theorem reverseGridIndex_injective (n : ℕ) : Function.Injective (reverseGridIndex n) := by
  intro i j hij
  apply fullAngle_injective (dyadic n)
  have hi := pi_sub_fullAngle_eq_index_mul_mesh n i
  have hj := pi_sub_fullAngle_eq_index_mul_mesh n j
  rw [hij] at hi
  linarith

theorem count_integer_mesh_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (angle : ι → ℝ) (index : ι → ℕ) (hinj : Function.Injective index)
    (hindex : ∀ i, 0 < index i) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hangle : ∀ i, angle i = (index i : ℝ) * δ) :
    ((Finset.univ.filter (fun i => angle i ≤ ε)).card : ℝ) * δ ≤ ε := by
  classical
  let F := Finset.univ.filter (fun i => angle i ≤ ε)
  have hmap : Set.MapsTo index (F : Set ι) (Finset.Icc 1 ⌊ε / δ⌋₊ : Set ℕ) := by
    intro i hi
    apply Finset.mem_Icc.mpr
    constructor
    · exact hindex i
    · apply Nat.le_floor
      apply (le_div_iff₀ hδ).mpr
      rw [← hangle i]
      exact (Finset.mem_filter.mp hi).2
  have hcard : F.card ≤ ⌊ε / δ⌋₊ := by
    have h := Finset.card_le_card_of_injOn index hmap hinj.injOn
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using h
  have hcast : (F.card : ℝ) ≤ (⌊ε / δ⌋₊ : ℝ) := by exact_mod_cast hcard
  have hbound : (F.card : ℝ) ≤ ε / δ :=
    hcast.trans (Nat.floor_le (div_nonneg hε hδ.le))
  exact (le_div_iff₀ hδ).mp hbound

theorem sum_mesh_right_sources_le (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    (∑ j ∈ Finset.univ.filter (fun j : SourceIndex (dyadic n) =>
      fullAngle (dyadic n) j ≤ ε), mesh n) ≤ ε := by
  classical
  simpa only [Finset.sum_const, nsmul_eq_mul] using
    count_integer_mesh_le (fullAngle (dyadic n)) (fullGridIndex n)
      (fullGridIndex_injective n) (fullGridIndex_pos n) (mesh_pos n) hε
      (fullAngle_eq_index_mul_mesh n)

theorem sum_mesh_left_sources_le (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    (∑ j ∈ Finset.univ.filter (fun j : SourceIndex (dyadic n) =>
      Real.pi - fullAngle (dyadic n) j ≤ ε), mesh n) ≤ ε := by
  classical
  simpa only [Finset.sum_const, nsmul_eq_mul] using
    count_integer_mesh_le (fun j => Real.pi - fullAngle (dyadic n) j) (reverseGridIndex n)
      (reverseGridIndex_injective n) (reverseGridIndex_pos n) (mesh_pos n) hε
      (pi_sub_fullAngle_eq_index_mul_mesh n)

/-- Distinct integer mesh points in a closed interval have at most one
mesh of endpoint rounding error. No alignment of either endpoint is
assumed. -/
theorem count_integer_mesh_interval_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (angle : ι → ℝ) (index : ι → ℕ) (hinj : Function.Injective index)
    {δ a b : ℝ} (hδ : 0 ≤ δ) (hab : a ≤ b)
    (hangle : ∀ i, angle i = (index i : ℝ) * δ) :
    ((Finset.univ.filter (fun i => angle i ∈ Icc a b)).card : ℝ) * δ ≤ b - a + δ := by
  classical
  let F := Finset.univ.filter (fun i => angle i ∈ Icc a b)
  by_cases hne : F.Nonempty
  · obtain ⟨i, hi, hmin⟩ := F.exists_min_image index hne
    obtain ⟨j, hj, hmax⟩ := F.exists_max_image index hne
    have hij : index i ≤ index j := hmin j hj
    have hmap : Set.MapsTo index (F : Set ι) (Finset.Icc (index i) (index j) : Set ℕ) := by
      intro k hk
      exact Finset.mem_Icc.mpr ⟨hmin k hk, hmax k hk⟩
    have hcard := Finset.card_le_card_of_injOn index hmap hinj.injOn
    rw [Nat.card_Icc] at hcard
    have hcast : (F.card : ℝ) ≤ (index j : ℝ) + 1 - (index i : ℝ) := by
      have hc : (F.card : ℝ) ≤ ((index j + 1 - index i : ℕ) : ℝ) := by exact_mod_cast hcard
      simpa only [Nat.cast_sub (by omega : index i ≤ index j + 1),
        Nat.cast_add, Nat.cast_one] using hc
    have hiab := (Finset.mem_filter.mp hi).2
    have hjab := (Finset.mem_filter.mp hj).2
    rw [hangle i] at hiab
    rw [hangle j] at hjab
    have hmul := mul_le_mul_of_nonneg_right hcast hδ
    nlinarith [hiab.1, hjab.2]
  · have hF : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change (F.card : ℝ) * δ ≤ _
    rw [hF]
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    linarith

theorem sum_mesh_interval_sources_le (n : ℕ) {a b : ℝ} (hab : a ≤ b) :
    (∑ j ∈ Finset.univ.filter (fun j : SourceIndex (dyadic n) =>
      fullAngle (dyadic n) j ∈ Icc a b), mesh n) ≤ b - a + mesh n := by
  classical
  simpa only [Finset.sum_const, nsmul_eq_mul] using
    count_integer_mesh_interval_le (fullAngle (dyadic n)) (fullGridIndex n)
      (fullGridIndex_injective n) (mesh_pos n).le hab (fullAngle_eq_index_mul_mesh n)

end AngularGrid

end AmbidextrousSofa
