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
    (q : Convexity.StdSimplex ℝ (Fin n) × (Fin n → S)) : Plane :=
  ∑ i, q.1.weights i • (q.2 i).1

/-- A finite compact parametrization of the actual convex hull: by planar Carathéodory, every
point of the hull is a convex combination of at most three points of `S`. -/
theorem actualHull_eq_iUnion_simplexRanges (S : Set Plane) :
    actualHull S = ⋃ n : Fin 4, range (hullSimplexMap S n.1) := by
  refine Subset.antisymm (fun x hx => ?_) (iUnion_subset fun n => ?_)
  · obtain ⟨ι, _, z, w, hzS, hzi, hw, hsum, rfl⟩ := eq_pos_convex_span_of_mem_convexHull hx
    have h : Fintype.card ι ≤ Module.finrank ℝ Plane + 1 :=
      hzi.card_le_finrank_succ.trans (Nat.succ_le_succ (Submodule.finrank_le _))
    simp only [Plane, Module.finrank_prod, Module.finrank_self] at h
    let e := (Fintype.equivFin ι).symm
    refine mem_iUnion.2 ⟨⟨Fintype.card ι, by omega⟩, (⟨Finsupp.equivFunOnFinite.symm
      fun i => w (e i), fun i => (hw _).le, ?_⟩, fun i => ⟨z (e i), hzS (mem_range_self _)⟩), ?_⟩
    · rw [Finsupp.sum_fintype _ _ fun _ => rfl]
      simpa only [Finsupp.coe_equivFunOnFinite_symm, e.sum_comp w] using hsum
    · simp only [hullSimplexMap, Finsupp.coe_equivFunOnFinite_symm]
      exact e.sum_comp fun i => w i • z i
  · rintro _ ⟨q, rfl⟩
    exact (convex_actualHull S).sum_mem (fun i _ => q.1.weights_nonneg i) q.1.total_of_fintype
      (fun i _ => subset_actualHull S (q.2 i).2)

/-- The actual convex hull of a compact planar set is compact, including the empty case. -/
theorem isCompact_actualHull {S : Set Plane} (hS : IsCompact S) :
    IsCompact (actualHull S) := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  rw [actualHull_eq_iUnion_simplexRanges]
  exact isCompact_iUnion fun n => isCompact_range (by unfold hullSimplexMap; fun_prop)

/-- A compact physical set in the unit strip has a genuine intrinsic upper hull cap. -/
theorem isDownwardCap_upper_actualHull {S : Set Plane} (hne : S.Nonempty)
    (hS : IsCompact S) (hstrip : S ⊆ unitStrip) :
    IsDownwardCap (upperCap (actualHull S)) :=
  isDownwardCap_upperCap (actualHull_nonempty hne) (isCompact_actualHull hS)
    (convex_actualHull S) (actualHull_subset_unitStrip hstrip)

end AmbidextrousSofa
