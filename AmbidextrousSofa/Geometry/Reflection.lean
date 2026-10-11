module

public import AmbidextrousSofa.Geometry.Support
public import AmbidextrousSofa.Geometry.HullCompact
public import AmbidextrousSofa.Geometry.Motions

@[expose] public section

/-!
# Reflection, physical projection, and the two actual hull caps

Reflection is the actual affine map `(x,y) ↦ (x,1-y)`. Its action on fibers,
supports, and convex hulls is proved directly. Connectedness ensures that the
original body's horizontal projection is already an interval, so convexifying
the body does not enlarge that projection.

The two hull caps are built from the actual hull and its actual reflection.
They retain their common projection, and their reflected intersection recovers
the hull as a literal set. No terminal-angle or sharp-area hypothesis is used.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem continuous_reflect : Continuous reflect := by unfold reflect; fun_prop

@[simp]
theorem mem_image_reflect (K : Set Plane) (p : Plane) : p ∈ reflect '' K ↔ reflect p ∈ K :=
  mem_image_iff_of_inverse reflect_reflect reflect_reflect

theorem image_reflect_eq_preimage (K : Set Plane) : reflect '' K = reflect ⁻¹' K :=
  ext (mem_image_reflect K)

theorem isCompact_image_reflect {K : Set Plane} (hK : IsCompact K) : IsCompact (reflect '' K) :=
  hK.image continuous_reflect

/-- Reflection as an affine map. -/
def reflectAffineMap : Plane →ᵃ[ℝ] Plane where
  toFun := reflect
  linear := LinearMap.prodMap LinearMap.id (-LinearMap.id)
  map_vadd' _ _ := Prod.ext rfl (by simp [reflect]; ring)

theorem convex_preimage_reflect {K : Set Plane} (hK : Convex ℝ K) : Convex ℝ (reflect ⁻¹' K) :=
  hK.affine_preimage reflectAffineMap

theorem image_reflect_subset_unitStrip {K : Set Plane} (hK : K ⊆ unitStrip) :
    reflect '' K ⊆ unitStrip :=
  image_subset_iff.2 fun q hq => (reflect_mem_unitStrip q).2 (hK hq)

/-- Affine reflection commutes with the actual convex hull. -/
theorem actualHull_reflect (S : Set Plane) :
    actualHull (reflect '' S) = reflect '' actualHull S :=
  (reflectAffineMap.image_convexHull S).symm

/-- Convexifying an actual connected compact body does not invent new abscissas. -/
theorem horizontalProjection_actualHull {S : Set Plane} (hcompact : IsCompact S)
    (hconnected : IsConnected S) :
    horizontalProjection (actualHull S) = horizontalProjection S :=
  have h : Convex ℝ (horizontalProjection S) :=
    horizontalProjection_eq_Icc_of_isConnected hcompact hconnected ▸ convex_Icc _ _
  ((LinearMap.fst ℝ ℝ ℝ).image_convexHull S).trans h.convexHull_eq

/-! ## Exact reflected fibers and support values -/

theorem convex_verticalFiber {K : Set Plane} (hK : Convex ℝ K) (x : ℝ) :
    Convex ℝ (verticalFiber K x) := fun y hy z hz a b ha hb hab => by
  simpa [verticalFiber, ← add_mul, hab] using hK hy hz ha hb hab

theorem support_reflect {K : Set Plane} (hK : IsCompact K) (hne : K.Nonempty)
    (v : Plane) : support (reflect '' K) v = support K (v.1, -v.2) + v.2 := by
  have h (p : Plane) : coordDot (reflect p) v = coordDot p (v.1, -v.2) + v.2 := by
    unfold coordDot reflect; ring
  obtain ⟨p, hp, hpmax⟩ := exists_coordDot_eq_support hK hne (v.1, -v.2)
  exact support_eq_of_mem (isCompact_image_reflect hK)
    (forall_mem_image.2 fun q hq => by linarith [h q, coordDot_le_support hK hq (v.1, -v.2)])
    (mem_image_of_mem reflect hp) (by rw [h, hpmax])

/-! ## The two caps retain the original hull and projection -/

def upperHullCap (S : Set Plane) : Set Plane := upperCap (actualHull S)

def reflectedHullCap (S : Set Plane) : Set Plane := upperCap (reflect '' actualHull S)

theorem isDownwardCap_upperHullCap {S : Set Plane} (hne : S.Nonempty)
    (hS : IsCompact S) (hstrip : S ⊆ unitStrip) : IsDownwardCap (upperHullCap S) :=
  isDownwardCap_upper_actualHull hne hS hstrip

theorem isDownwardCap_reflectedHullCap {S : Set Plane} (hne : S.Nonempty)
    (hS : IsCompact S) (hstrip : S ⊆ unitStrip) : IsDownwardCap (reflectedHullCap S) :=
  isDownwardCap_upperCap ((actualHull_nonempty hne).image reflect)
    (isCompact_image_reflect (isCompact_actualHull hS))
    ((convex_actualHull S).affine_image reflectAffineMap)
    (image_reflect_subset_unitStrip (actualHull_subset_unitStrip hstrip))

theorem horizontalProjection_hullCaps {S : Set Plane} (hstrip : S ⊆ unitStrip) :
    horizontalProjection (upperHullCap S) = horizontalProjection (actualHull S) ∧
      horizontalProjection (reflectedHullCap S) = horizontalProjection (actualHull S) :=
  ⟨horizontalProjection_upperCap fun _ hp => (actualHull_subset_unitStrip hstrip hp).1,
    (horizontalProjection_upperCap fun _ hp =>
      (image_reflect_subset_unitStrip (actualHull_subset_unitStrip hstrip) hp).1).trans
      (image_image Prod.fst reflect _)⟩

theorem hullCaps_same_horizontalProjection {S : Set Plane} (hstrip : S ⊆ unitStrip) :
    horizontalProjection (upperHullCap S) = horizontalProjection (reflectedHullCap S) :=
  (horizontalProjection_hullCaps hstrip).1.trans (horizontalProjection_hullCaps hstrip).2.symm

/-- Both scalar caps use the actual connected body's entire projection. -/
theorem hullCaps_horizontalProjection_eq_original {S : Set Plane} (hS : IsCompact S)
    (hconnected : IsConnected S) (hstrip : S ⊆ unitStrip) :
    horizontalProjection (upperHullCap S) = horizontalProjection S ∧
      horizontalProjection (reflectedHullCap S) = horizontalProjection S := by
  rw [← horizontalProjection_actualHull hS hconnected]
  exact horizontalProjection_hullCaps hstrip

/-- A convex set in the strip is literally the overlap of its two downward caps. -/
theorem eq_upperCap_inter_reflectedCap {K : Set Plane} (hconvex : Convex ℝ K)
    (hstrip : K ⊆ unitStrip) :
    K = upperCap K ∩ reflect '' upperCap (reflect '' K) := by
  refine Subset.antisymm (fun p hp => ⟨subset_upperCap (fun _ hq => (hstrip hq).1) hp,
    reflect p, subset_upperCap (fun _ hq => (image_reflect_subset_unitStrip hstrip hq).1)
      (mem_image_of_mem reflect hp), reflect_reflect p⟩) ?_
  rintro p ⟨⟨-, u, hpu, hu⟩, hlower⟩
  obtain ⟨-, l, hpl, hl⟩ := (mem_image_reflect _ p).1 hlower
  simp only [reflect, mem_image_reflect] at hpl hl
  exact (convex_verticalFiber hconvex p.1).ordConnected.out hl hu ⟨by linarith, hpu⟩

/-- The two cap constructions recover the actual hull, including every boundary point. -/
theorem actualHull_eq_inter_hullCaps {S : Set Plane} (hstrip : S ⊆ unitStrip) :
    actualHull S = upperHullCap S ∩ reflect '' reflectedHullCap S :=
  eq_upperCap_inter_reflectedCap (convex_actualHull S) (actualHull_subset_unitStrip hstrip)

/-- The original point lies below the upper roof and above the reflected lower roof. -/
theorem originalPoint_roof_bounds {S : Set Plane} (hS : IsCompact S)
    (hstrip : S ⊆ unitStrip) {p : Plane} (hp : p ∈ S) :
    1 - capRoof (reflectedHullCap S) p.1 ≤ p.2 ∧
      p.2 ≤ capRoof (upperHullCap S) p.1 := by
  have h := (actualHull_eq_inter_hullCaps hstrip).subset (subset_actualHull S hp)
  have hl := le_capRoof (isDownwardCap_reflectedHullCap ⟨p, hp⟩ hS hstrip).isCompact
    ((mem_image_reflect _ p).1 h.2)
  exact ⟨by linarith, le_capRoof (isDownwardCap_upperHullCap ⟨p, hp⟩ hS hstrip).isCompact h.1⟩

end AmbidextrousSofa
