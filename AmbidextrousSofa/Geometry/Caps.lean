module

public import AmbidextrousSofa.Geometry.Plane

@[expose] public section

/-!
# Actual convex hulls and downward caps

`IsDownwardCap` describes the broad scalar domain: nonempty compact convex
sets in the unit strip, closed downward to the baseline. It permits subunit
height, zero width, asymmetry, and nonsmooth boundary.

`upperCap` fills vertically down from a set. The lemmas below establish its
elementary containment, projection, and fixed-point properties. Compactness,
convexity, support functions, and integral scores for hull-derived caps remain
separate formalization tasks.
-/

namespace AmbidextrousSofa

/-- The actual convex hull of the original physical set. -/
def actualHull (S : Set Plane) : Set Plane := convexHull ℝ S

/-- Horizontal projection as a set, without assuming a nondegenerate interval. -/
def horizontalProjection (S : Set Plane) : Set ℝ := Prod.fst '' S

/-- Downward closure to the baseline. Points below the baseline are discarded. -/
def upperCap (K : Set Plane) : Set Plane :=
  {p | 0 ≤ p.2 ∧ ∃ y : ℝ, p.2 ≤ y ∧ (p.1, y) ∈ K}

/-- The intrinsic cap domain, with height at most one rather than exactly one. -/
structure IsDownwardCap (U : Set Plane) : Prop where
  nonempty : U.Nonempty
  isCompact : IsCompact U
  convex : Convex ℝ U
  inStrip : U ⊆ unitStrip
  downward : ∀ p ∈ U, ∀ y : ℝ, 0 ≤ y → y ≤ p.2 → (p.1, y) ∈ U

theorem subset_actualHull (S : Set Plane) : S ⊆ actualHull S :=
  subset_convexHull ℝ S

theorem convex_actualHull (S : Set Plane) : Convex ℝ (actualHull S) :=
  convex_convexHull ℝ S

theorem actualHull_mono {S T : Set Plane} (hST : S ⊆ T) :
    actualHull S ⊆ actualHull T :=
  convexHull_mono hST

theorem upperCap_mono {K L : Set Plane} (hKL : K ⊆ L) : upperCap K ⊆ upperCap L := by
  rintro p ⟨hp0, y, hpy, hy⟩
  exact ⟨hp0, y, hpy, hKL hy⟩

/-- Every upper cap is closed downward within the nonnegative half-plane. -/
theorem upperCap_downward {K : Set Plane} {p : Plane} (hp : p ∈ upperCap K)
    {y : ℝ} (hy0 : 0 ≤ y) (hyp : y ≤ p.2) : (p.1, y) ∈ upperCap K := by
  obtain ⟨_, z, hpz, hz⟩ := hp
  exact ⟨hy0, z, hyp.trans hpz, hz⟩

/-- A set above the baseline is contained in its own upper cap. -/
theorem subset_upperCap {K : Set Plane} (hK : ∀ p ∈ K, 0 ≤ p.2) : K ⊆ upperCap K := by
  intro p hp
  refine ⟨hK p hp, p.2, le_rfl, ?_⟩
  simpa only [Prod.mk.eta] using hp

/-- Vertical downward filling preserves the exact horizontal projection. -/
theorem horizontalProjection_upperCap {K : Set Plane} (hK : ∀ p ∈ K, 0 ≤ p.2) :
    horizontalProjection (upperCap K) = horizontalProjection K := by
  apply Set.Subset.antisymm
  · rintro x ⟨p, hp, hpx⟩
    obtain ⟨_, y, _, hy⟩ := hp
    exact ⟨(p.1, y), hy, hpx⟩
  · rintro x ⟨p, hp, hpx⟩
    exact ⟨p, subset_upperCap hK hp, hpx⟩

/-- An intrinsic downward cap is already fixed by downward filling. -/
theorem IsDownwardCap.upperCap_eq {U : Set Plane} (hU : IsDownwardCap U) :
    upperCap U = U := by
  apply Set.Subset.antisymm
  · rintro p ⟨hp0, y, hpy, hy⟩
    have hp : (p.1, p.2) ∈ U := hU.downward (p.1, y) hy p.2 hp0 hpy
    simpa only [Prod.mk.eta] using hp
  · exact subset_upperCap (fun p hp => (hU.inStrip hp).1)

/-- The baseline point under any cap point remains in the cap. -/
theorem IsDownwardCap.baseline_mem {U : Set Plane} (hU : IsDownwardCap U)
    {p : Plane} (hp : p ∈ U) : (p.1, 0) ∈ U :=
  hU.downward p hp 0 le_rfl (hU.inStrip hp).1

end AmbidextrousSofa
