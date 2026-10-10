module

public import AmbidextrousSofa.Geometry.CapGeometry

@[expose] public section

/-!
# Compactness of the actual planar convex hull

Carathéodory's theorem gives at most three points in a planar convex
combination. We express the actual convex hull as a finite union of images
of compact simplices times finite powers of the original compact set.
This proves compactness of `actualHull S`; closedness is not assumed.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

/-- A convex combination of `n` actual points of `S`. -/
def hullSimplexMap (S : Set Plane) (n : ℕ)
    (q : stdSimplex ℝ (Fin n) × (Fin n → S)) : Plane :=
  ∑ i, q.1.1 i • (q.2 i).1

theorem continuous_hullSimplexMap (S : Set Plane) (n : ℕ) :
    Continuous (hullSimplexMap S n) := by
  unfold hullSimplexMap
  apply continuous_finset_sum
  intro i _
  exact ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).smul
    (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd))

/-- Every simplex combination stays in the actual convex hull. -/
theorem hullSimplexMap_mem_actualHull (S : Set Plane) (n : ℕ)
    (q : stdSimplex ℝ (Fin n) × (Fin n → S)) :
    hullSimplexMap S n q ∈ actualHull S := by
  exact (convex_actualHull S).sum_mem
    (fun i _ => q.1.2.1 i) q.1.2.2
    (fun i _ => subset_actualHull S (q.2 i).2)

/-- The dimension bound used by planar Carathéodory. -/
theorem card_le_three_of_affineIndependent {ι : Type} [Fintype ι]
    {p : ι → Plane} (hp : AffineIndependent ℝ p) : Fintype.card ι ≤ 3 := by
  have hcard := hp.card_le_finrank_succ
  have hdim : Module.finrank ℝ (vectorSpan ℝ (Set.range p)) ≤ 2 := by
    have h := (vectorSpan ℝ (Set.range p)).finrank_le
    simpa [Plane] using h
  omega

/-- Every point in the hull has a convex combination with at most three terms. -/
theorem exists_hullSimplexMap_of_mem {S : Set Plane} {x : Plane}
    (hx : x ∈ actualHull S) :
    ∃ n : Fin 4, x ∈ Set.range (hullSimplexMap S n.1) := by
  classical
  obtain ⟨ι, hι, z, w, hzS, hzi, hw, hsum, hcombo⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx
  letI := hι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hcard : Fintype.card ι < 4 := by
    have h := card_le_three_of_affineIndependent hzi
    omega
  let w' : Fin (Fintype.card ι) → ℝ := fun i => w (e.symm i)
  let z' : Fin (Fintype.card ι) → S := fun i =>
    ⟨z (e.symm i), hzS (Set.mem_range_self _)⟩
  have hw' : ∀ i, 0 ≤ w' i := fun i => (hw (e.symm i)).le
  have hsum' : ∑ i, w' i = 1 := by
    change (∑ i, w (e.symm i)) = 1
    rw [Equiv.sum_comp e.symm w]
    exact hsum
  have hcombo' : (∑ i, w' i • (z' i).1) = x := by
    change (∑ i, w (e.symm i) • z (e.symm i)) = x
    rw [Equiv.sum_comp e.symm (fun i => w i • z i)]
    exact hcombo
  refine ⟨⟨Fintype.card ι, hcard⟩, ?_⟩
  exact ⟨(⟨w', hw', hsum'⟩, z'), hcombo'⟩

/-- A finite compact parametrization of the actual convex hull. -/
theorem actualHull_eq_iUnion_simplexRanges (S : Set Plane) :
    actualHull S = ⋃ n : Fin 4, Set.range (hullSimplexMap S n.1) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨n, hn⟩ := exists_hullSimplexMap_of_mem hx
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  · intro x hx
    obtain ⟨n, q, rfl⟩ := Set.mem_iUnion.mp hx
    exact hullSimplexMap_mem_actualHull S n.1 q

/-- The actual convex hull of a compact planar set is compact, including the empty case. -/
theorem isCompact_actualHull {S : Set Plane} (hS : IsCompact S) :
    IsCompact (actualHull S) := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  rw [actualHull_eq_iUnion_simplexRanges]
  apply isCompact_iUnion
  intro n
  exact isCompact_range (continuous_hullSimplexMap S n.1)

/-- A compact physical set in the unit strip has a genuine intrinsic upper hull cap. -/
theorem isDownwardCap_upper_actualHull {S : Set Plane} (hne : S.Nonempty)
    (hS : IsCompact S) (hstrip : S ⊆ unitStrip) :
    IsDownwardCap (upperCap (actualHull S)) :=
  isDownwardCap_upperCap (actualHull_nonempty hne) (isCompact_actualHull hS)
    (convex_actualHull S) (actualHull_subset_unitStrip hstrip)

end AmbidextrousSofa
