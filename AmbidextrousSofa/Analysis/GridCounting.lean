module

public import AmbidextrousSofa.Analysis.DyadicNeighbors

@[expose] public section

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

theorem divisions_mul_mesh (n : ℕ) : (divisions n : ℝ) * mesh n = Real.pi / 2 :=
  mul_div_cancel₀ _ (by exact_mod_cast (divisions_pos n).ne')

theorem interior_dyadic_index (n : ℕ) (t : InteriorPoint (dyadic n)) :
    ∃ i : ℕ, 0 < i ∧ i < divisions n ∧ (t.val : ℝ) = (i : ℝ) * mesh n := by
  obtain ⟨i, hi, hti⟩ := (mem_dyadic_iff n t.val).mp (interiorPoint_mem_grid _ t)
  obtain ⟨h0, h1⟩ := interiorPoint_mem (dyadic n) t
  replace hti : (t.val : ℝ) = i * mesh n := by rw [hti, mesh]; ring
  refine ⟨i, Nat.pos_of_ne_zero ?_, hi.lt_of_ne ?_, hti⟩ <;> rintro rfl
  · simp at hti; linarith
  · linarith [divisions_mul_mesh n]

theorem fullAngle_integer_mesh (n : ℕ) (j : SourceIndex (dyadic n)) :
    ∃ i : ℕ, 0 < i ∧ i < 2 * divisions n ∧
      fullAngle (dyadic n) j = (i : ℝ) * mesh n := by
  rcases j with t | t <;> obtain ⟨i, hi0, hiN, ht⟩ := interior_dyadic_index n t
  · exact ⟨i, hi0, by omega, ht⟩
  · refine ⟨i + divisions n, by omega, by omega, ?_⟩
    simp only [fullAngle, ht, Nat.cast_add, add_mul, divisions_mul_mesh]

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

theorem fullGridIndex_injective (n : ℕ) : Function.Injective (fullGridIndex n) := fun i j hij =>
  fullAngle_injective (dyadic n) (by
    rw [fullAngle_eq_index_mul_mesh, fullAngle_eq_index_mul_mesh, hij])

theorem count_integer_mesh_le {ι : Type*} [Fintype ι]
    (angle : ι → ℝ) (index : ι → ℕ) (hinj : Function.Injective index)
    (hindex : ∀ i, 0 < index i) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hangle : ∀ i, angle i = (index i : ℝ) * δ) :
    ((Finset.univ.filter (fun i => angle i ≤ ε)).card : ℝ) * δ ≤ ε := by
  have hcard := Finset.card_le_card_of_injOn index (s := Finset.univ.filter (angle · ≤ ε))
    (t := Finset.Icc 1 ⌊ε / δ⌋₊) (fun i hi => Finset.mem_Icc.mpr ⟨hindex i,
      Nat.le_floor ((le_div_iff₀ hδ).mpr (hangle i ▸ (Finset.mem_filter.mp hi).2))⟩) hinj.injOn
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hcard
  rw [← le_div_iff₀ hδ]
  exact (Nat.cast_le.mpr hcard).trans (Nat.floor_le (div_nonneg hε hδ.le))

theorem sum_mesh_right_sources_le (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    (∑ _j ∈ Finset.univ.filter (fun j : SourceIndex (dyadic n) =>
      fullAngle (dyadic n) j ≤ ε), mesh n) ≤ ε := by
  simpa only [Finset.sum_const, nsmul_eq_mul] using
    count_integer_mesh_le (fullAngle (dyadic n)) (fullGridIndex n) (fullGridIndex_injective n)
      (fullGridIndex_pos n) (mesh_pos n) hε (fullAngle_eq_index_mul_mesh n)

theorem sum_mesh_left_sources_le (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    (∑ _j ∈ Finset.univ.filter (fun j : SourceIndex (dyadic n) =>
      Real.pi - fullAngle (dyadic n) j ≤ ε), mesh n) ≤ ε := by
  have hlt := fullGridIndex_lt n
  simpa only [Finset.sum_const, nsmul_eq_mul] using
    count_integer_mesh_le (fun j => Real.pi - fullAngle (dyadic n) j)
      (fun j => 2 * divisions n - fullGridIndex n j)
      (fun i j h => fullGridIndex_injective n (by
        have := hlt i; have := hlt j; simp only at h; omega))
      (fun j => Nat.sub_pos_of_lt (hlt j)) (mesh_pos n) hε fun j => by
        rw [fullAngle_eq_index_mul_mesh, Nat.cast_sub (hlt j).le]
        push_cast
        linarith [divisions_mul_mesh n]

open Classical in
/-- Distinct integer mesh points in a closed interval have at most one
mesh of endpoint rounding error. No alignment of either endpoint is
assumed. -/
theorem count_integer_mesh_interval_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (angle : ι → ℝ) (index : ι → ℕ) (hinj : Function.Injective index)
    {δ a b : ℝ} (hδ : 0 ≤ δ) (hab : a ≤ b)
    (hangle : ∀ i, angle i = (index i : ℝ) * δ) :
    ((Finset.univ.filter (fun i => angle i ∈ Icc a b)).card : ℝ) * δ ≤ b - a + δ := by
  set F := Finset.univ.filter (fun i => angle i ∈ Icc a b)
  rcases F.eq_empty_or_nonempty with hF | hne
  · simp only [hF, Finset.card_empty, Nat.cast_zero, zero_mul]
    linarith
  obtain ⟨i, hi, hmin⟩ := F.exists_min_image index hne
  obtain ⟨j, hj, hmax⟩ := F.exists_max_image index hne
  have hcard := Finset.card_le_card_of_injOn index (t := Finset.Icc (index i) (index j))
    (fun k hk => Finset.mem_Icc.mpr ⟨hmin k hk, hmax k hk⟩) hinj.injOn
  rw [Nat.card_Icc] at hcard
  have hij := hmin j hj
  have hcast : (F.card : ℝ) ≤ index j + 1 - index i := by
    have := Nat.cast_le (α := ℝ).mpr hcard
    rwa [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one] at this
  have hiab := (Finset.mem_filter.mp hi).2
  have hjab := (Finset.mem_filter.mp hj).2
  rw [hangle] at hiab hjab
  linarith [mul_le_mul_of_nonneg_right hcast hδ, hiab.1, hjab.2]

open Classical in
theorem sum_mesh_interval_sources_le (n : ℕ) {a b : ℝ} (hab : a ≤ b) :
    (∑ _j ∈ Finset.univ.filter (fun j : SourceIndex (dyadic n) =>
      fullAngle (dyadic n) j ∈ Icc a b), mesh n) ≤ b - a + mesh n := by
  simpa only [Finset.sum_const, nsmul_eq_mul] using
    count_integer_mesh_interval_le (fullAngle (dyadic n)) (fullGridIndex n)
      (fullGridIndex_injective n) (mesh_pos n).le hab (fullAngle_eq_index_mul_mesh n)

end AngularGrid

end AmbidextrousSofa
