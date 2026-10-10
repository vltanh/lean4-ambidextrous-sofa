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

theorem continuous_reflect : Continuous reflect := by
  unfold reflect
  fun_prop

@[simp]
theorem mem_image_reflect (K : Set Plane) (p : Plane) :
    p ∈ reflect '' K ↔ reflect p ∈ K := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa only [reflect_reflect] using hq
  · intro hp
    exact ⟨reflect p, hp, reflect_reflect p⟩

theorem image_reflect_eq_preimage (K : Set Plane) :
    reflect '' K = reflect ⁻¹' K := by
  ext p
  exact mem_image_reflect K p

theorem isCompact_image_reflect {K : Set Plane} (hK : IsCompact K) :
    IsCompact (reflect '' K) :=
  hK.image continuous_reflect

/-- Reflection preserves affine combinations whose weights sum to one. -/
theorem reflect_combo (p q : Plane) (a b : ℝ) (hab : a + b = 1) :
    reflect (a • p + b • q) = a • reflect p + b • reflect q := by
  apply Prod.ext
  · rfl
  · change 1 - (a * p.2 + b * q.2) = a * (1 - p.2) + b * (1 - q.2)
    nlinarith [hab]

theorem convex_image_reflect {K : Set Plane} (hK : Convex ℝ K) :
    Convex ℝ (reflect '' K) := by
  rintro p ⟨p', hp, rfl⟩ q ⟨q', hq, rfl⟩ a b ha hb hab
  exact ⟨a • p' + b • q', hK hp hq ha hb hab, reflect_combo p' q' a b hab⟩

theorem convex_preimage_reflect {K : Set Plane} (hK : Convex ℝ K) :
    Convex ℝ (reflect ⁻¹' K) := by
  intro p hp q hq a b ha hb hab
  change reflect (a • p + b • q) ∈ K
  rw [reflect_combo p q a b hab]
  exact hK hp hq ha hb hab

theorem image_reflect_subset_unitStrip {K : Set Plane} (hK : K ⊆ unitStrip) :
    reflect '' K ⊆ unitStrip := by
  rintro p ⟨q, hq, rfl⟩
  exact (reflect_mem_unitStrip q).mpr (hK hq)

/-- Affine reflection commutes with the actual convex hull. -/
theorem actualHull_reflect (S : Set Plane) :
    actualHull (reflect '' S) = reflect '' actualHull S := by
  apply Set.Subset.antisymm
  · apply convexHull_min ?_ (convex_image_reflect (convex_actualHull S))
    rintro p ⟨q, hq, rfl⟩
    exact ⟨q, subset_actualHull S hq, rfl⟩
  · rintro p ⟨q, hq, rfl⟩
    have hpre : actualHull S ⊆ reflect ⁻¹' actualHull (reflect '' S) := by
      apply convexHull_min ?_ (convex_preimage_reflect (convex_actualHull (reflect '' S)))
      intro q hq
      exact subset_actualHull (reflect '' S) (mem_image_of_mem reflect hq)
    exact hpre hq

@[simp]
theorem horizontalProjection_reflect (K : Set Plane) :
    horizontalProjection (reflect '' K) = horizontalProjection K := by
  unfold horizontalProjection
  rw [Set.image_image]
  rfl

/-- The horizontal image of a connected compact physical body is its exact closed interval. -/
theorem horizontalProjection_eq_Icc_of_isConnected {S : Set Plane}
    (hcompact : IsCompact S) (hconnected : IsConnected S) :
    horizontalProjection S = Icc (horizontalLeft S) (horizontalRight S) :=
  eq_Icc_of_connected_compact
    (hconnected.image Prod.fst continuous_fst.continuousOn)
    (isCompact_horizontalProjection hcompact)

/-- Convexifying an actual connected compact body does not invent new abscissas. -/
theorem horizontalProjection_actualHull {S : Set Plane} (hcompact : IsCompact S)
    (hconnected : IsConnected S) :
    horizontalProjection (actualHull S) = horizontalProjection S := by
  have hprojection : Convex ℝ (horizontalProjection S) := by
    rw [horizontalProjection_eq_Icc_of_isConnected hcompact hconnected]
    exact convex_Icc _ _
  have hpre : Convex ℝ ((Prod.fst : Plane → ℝ) ⁻¹' horizontalProjection S) := by
    intro p hp q hq a b ha hb hab
    exact hprojection hp hq ha hb hab
  have hhull : actualHull S ⊆ Prod.fst ⁻¹' horizontalProjection S :=
    convexHull_min (fun p hp => ⟨p, hp, rfl⟩) hpre
  apply Set.Subset.antisymm
  · rintro x ⟨p, hp, rfl⟩
    exact hhull hp
  · exact image_mono (subset_actualHull S)

theorem IsAmbidextrous.horizontalProjection_actualHull {S : Set Plane}
    (hS : IsAmbidextrous S) :
    horizontalProjection (actualHull S) = horizontalProjection S :=
  AmbidextrousSofa.horizontalProjection_actualHull hS.isCompact hS.isConnected

/-! ## Exact reflected fibers and support values -/

theorem convex_verticalFiber {K : Set Plane} (hK : Convex ℝ K) (x : ℝ) :
    Convex ℝ (verticalFiber K x) := by
  intro y hy z hz a b ha hb hab
  have hcomb := hK hy hz ha hb hab
  have hx : a * x + b * x = x := by rw [← add_mul, hab, one_mul]
  change (x, a * y + b * z) ∈ K
  simpa [smul_eq_mul, hx] using hcomb

theorem coordDot_reflect (p v : Plane) :
    coordDot (reflect p) v = coordDot p (v.1, -v.2) + v.2 := by
  unfold coordDot reflect
  ring

theorem support_reflect {K : Set Plane} (hK : IsCompact K) (hne : K.Nonempty)
    (v : Plane) : support (reflect '' K) v = support K (v.1, -v.2) + v.2 := by
  have hreflection := isCompact_image_reflect hK
  apply le_antisymm
  · apply support_le_of_forall (hne.image reflect)
    rintro q ⟨p, hp, rfl⟩
    rw [coordDot_reflect]
    exact add_le_add_left (coordDot_le_support hK hp (v.1, -v.2)) _
  · obtain ⟨p, hp, hpmax⟩ := exists_coordDot_eq_support hK hne (v.1, -v.2)
    calc
      support K (v.1, -v.2) + v.2 = coordDot (reflect p) v := by
        rw [coordDot_reflect, hpmax]
      _ ≤ support (reflect '' K) v :=
        coordDot_le_support hreflection (mem_image_of_mem reflect hp) v

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
    (convex_image_reflect (convex_actualHull S))
    (image_reflect_subset_unitStrip (actualHull_subset_unitStrip hstrip))

theorem subset_upperHullCap {S : Set Plane} (hstrip : S ⊆ unitStrip) :
    S ⊆ upperHullCap S := by
  intro p hp
  exact subset_upperCap (fun q hq => (actualHull_subset_unitStrip hstrip hq).1)
    (subset_actualHull S hp)

theorem reflect_mem_reflectedHullCap {S : Set Plane} (hstrip : S ⊆ unitStrip)
    {p : Plane} (hp : p ∈ S) : reflect p ∈ reflectedHullCap S := by
  exact subset_upperCap
    (fun q hq => (image_reflect_subset_unitStrip (actualHull_subset_unitStrip hstrip) hq).1)
    (mem_image_of_mem reflect (subset_actualHull S hp))

/-- The original point lies below the upper roof and above the reflected lower roof. -/
theorem originalPoint_roof_bounds {S : Set Plane} (hS : IsCompact S)
    (hstrip : S ⊆ unitStrip) {p : Plane} (hp : p ∈ S) :
    1 - capRoof (reflectedHullCap S) p.1 ≤ p.2 ∧
      p.2 ≤ capRoof (upperHullCap S) p.1 := by
  have hU := isDownwardCap_upperHullCap ⟨p, hp⟩ hS hstrip
  have hV := isDownwardCap_reflectedHullCap ⟨p, hp⟩ hS hstrip
  have hlower : 1 - p.2 ≤ capRoof (reflectedHullCap S) p.1 :=
    le_capRoof hV.isCompact (reflect_mem_reflectedHullCap hstrip hp)
  refine ⟨by linarith, ?_⟩
  apply le_capRoof hU.isCompact
  simpa only [Prod.mk.eta] using subset_upperHullCap hstrip hp

theorem horizontalProjection_upperHullCap {S : Set Plane} (hstrip : S ⊆ unitStrip) :
    horizontalProjection (upperHullCap S) = horizontalProjection (actualHull S) :=
  horizontalProjection_upperCap (fun p hp => (actualHull_subset_unitStrip hstrip hp).1)

theorem horizontalProjection_reflectedHullCap {S : Set Plane} (hstrip : S ⊆ unitStrip) :
    horizontalProjection (reflectedHullCap S) = horizontalProjection (actualHull S) := by
  unfold reflectedHullCap
  rw [horizontalProjection_upperCap
    (fun p hp => (image_reflect_subset_unitStrip (actualHull_subset_unitStrip hstrip) hp).1),
    horizontalProjection_reflect]

theorem hullCaps_same_horizontalProjection {S : Set Plane} (hstrip : S ⊆ unitStrip) :
    horizontalProjection (upperHullCap S) = horizontalProjection (reflectedHullCap S) := by
  rw [horizontalProjection_upperHullCap hstrip, horizontalProjection_reflectedHullCap hstrip]

/-- Both scalar caps use the actual connected body's entire projection. -/
theorem hullCaps_horizontalProjection_eq_original {S : Set Plane} (hS : IsCompact S)
    (hconnected : IsConnected S) (hstrip : S ⊆ unitStrip) :
    horizontalProjection (upperHullCap S) = horizontalProjection S ∧
      horizontalProjection (reflectedHullCap S) = horizontalProjection S := by
  rw [horizontalProjection_upperHullCap hstrip, horizontalProjection_reflectedHullCap hstrip,
    horizontalProjection_actualHull hS hconnected]
  exact ⟨rfl, rfl⟩

/-- A convex set in the strip is literally the overlap of its two downward caps. -/
theorem eq_upperCap_inter_reflectedCap {K : Set Plane} (hconvex : Convex ℝ K)
    (hstrip : K ⊆ unitStrip) :
    K = upperCap K ∩ reflect '' upperCap (reflect '' K) := by
  apply Set.Subset.antisymm
  · intro p hp
    refine ⟨subset_upperCap (fun q hq => (hstrip hq).1) hp, ?_⟩
    apply (mem_image_reflect (upperCap (reflect '' K)) p).mpr
    exact subset_upperCap
      (fun q hq => (image_reflect_subset_unitStrip hstrip hq).1)
      (mem_image_of_mem reflect hp)
  · rintro p ⟨hupper, hlower⟩
    obtain ⟨_, upper, hpUpper, hUpper⟩ := hupper
    have hreflect : reflect p ∈ upperCap (reflect '' K) :=
      (mem_image_reflect (upperCap (reflect '' K)) p).mp hlower
    obtain ⟨_, reflectedLower, hpLower, hLower⟩ := hreflect
    have hLowerOriginal : (p.1, 1 - reflectedLower) ∈ K :=
      (mem_image_reflect K (p.1, reflectedLower)).mp hLower
    have hbetween : p.2 ∈ Icc (1 - reflectedLower) upper :=
      ⟨by change 1 - p.2 ≤ reflectedLower at hpLower; linarith, hpUpper⟩
    have hp : (p.1, p.2) ∈ K :=
      (convex_verticalFiber hconvex p.1).ordConnected.out hLowerOriginal hUpper hbetween
    simpa only [Prod.mk.eta] using hp

/-- The two cap constructions recover the actual hull, including every boundary point. -/
theorem actualHull_eq_inter_hullCaps {S : Set Plane} (hstrip : S ⊆ unitStrip) :
    actualHull S = upperHullCap S ∩ reflect '' reflectedHullCap S :=
  eq_upperCap_inter_reflectedCap (convex_actualHull S) (actualHull_subset_unitStrip hstrip)

end AmbidextrousSofa
