module

public import AmbidextrousSofa.Geometry.Caps

@[expose] public section

/-!
# Compact caps, exact vertical fibers, and roofs

The cap construction is carried out on actual sets. Compactness of downward
filling follows from a continuous image of the original compact set times
`[0, 1]`. No smoothness, positive width, or height-one hypothesis is used.

The roof is extended by zero outside its exact horizontal projection. This
extension is upper semicontinuous for a compact set above the baseline. For
an intrinsic downward cap, its fibers are exactly the intervals from zero to
the roof, and convexity makes the roof concave on its projection.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem convex_unitStrip : Convex ℝ unitStrip := by
  intro p hp q hq a b ha hb hab
  change 0 ≤ a * p.2 + b * q.2 ∧ a * p.2 + b * q.2 ≤ 1
  refine ⟨add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1), ?_⟩
  calc
    a * p.2 + b * q.2 ≤ a * 1 + b * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left hp.2 ha)
        (mul_le_mul_of_nonneg_left hq.2 hb)
    _ = 1 := by simpa only [mul_one] using hab

theorem actualHull_subset_unitStrip {S : Set Plane} (hS : S ⊆ unitStrip) :
    actualHull S ⊆ unitStrip :=
  convexHull_min hS convex_unitStrip

theorem actualHull_nonempty {S : Set Plane} (hS : S.Nonempty) :
    (actualHull S).Nonempty :=
  hS.mono (subset_actualHull S)

/-- Downward filling is parametrized by vertical contraction to the baseline. -/
theorem upperCap_eq_image {K : Set Plane} (hK : ∀ p ∈ K, 0 ≤ p.2) :
    upperCap K =
      (fun z : Plane × ℝ => (z.1.1, z.2 * z.1.2)) ''
        (K ×ˢ Icc (0 : ℝ) 1) := by
  apply Set.Subset.antisymm
  · rintro p ⟨hp0, y, hpy, hy⟩
    have hy0 : 0 ≤ y := hK (p.1, y) hy
    by_cases hyzero : y = 0
    · have hpzero : p.2 = 0 := le_antisymm (by simpa [hyzero] using hpy) hp0
      refine ⟨((p.1, y), 0), ⟨hy, by simp⟩, ?_⟩
      apply Prod.ext
      · rfl
      · simpa only [zero_mul] using hpzero.symm
    · have hypos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hyzero)
      refine ⟨((p.1, y), p.2 / y),
        ⟨hy, div_nonneg hp0 hy0, (div_le_one hypos).2 hpy⟩, ?_⟩
      apply Prod.ext
      · rfl
      · change p.2 / y * y = p.2
        exact div_mul_cancel₀ _ hyzero
  · rintro p ⟨⟨q, t⟩, ⟨hq, ht⟩, rfl⟩
    refine ⟨mul_nonneg ht.1 (hK q hq), q.2, ?_, ?_⟩
    · simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 (hK q hq)
    · simpa only [Prod.mk.eta] using hq

/-- Compactness is proved for the actual downward-filled set. -/
theorem isCompact_upperCap {K : Set Plane} (hK : IsCompact K)
    (hK0 : ∀ p ∈ K, 0 ≤ p.2) : IsCompact (upperCap K) := by
  rw [upperCap_eq_image hK0]
  exact (hK.prod isCompact_Icc).image (by fun_prop)

theorem convex_upperCap {K : Set Plane} (hK : Convex ℝ K) :
    Convex ℝ (upperCap K) := by
  intro p hp q hq a b ha hb hab
  obtain ⟨hp0, yp, hpyp, hyp⟩ := hp
  obtain ⟨hq0, yq, hqyq, hyq⟩ := hq
  refine ⟨?_, a * yp + b * yq, ?_, ?_⟩
  · change 0 ≤ a * p.2 + b * q.2
    exact add_nonneg (mul_nonneg ha hp0) (mul_nonneg hb hq0)
  · change a * p.2 + b * q.2 ≤ a * yp + b * yq
    exact add_le_add (mul_le_mul_of_nonneg_left hpyp ha)
      (mul_le_mul_of_nonneg_left hqyq hb)
  · simpa [smul_eq_mul] using hK hyp hyq ha hb hab

theorem upperCap_subset_unitStrip {K : Set Plane} (hK : K ⊆ unitStrip) :
    upperCap K ⊆ unitStrip := by
  rintro p ⟨hp0, y, hpy, hy⟩
  exact ⟨hp0, hpy.trans (hK hy).2⟩

/-- Every nonempty compact convex hull in the strip produces an intrinsic cap. -/
theorem isDownwardCap_upperCap {K : Set Plane} (hne : K.Nonempty)
    (hcompact : IsCompact K) (hconvex : Convex ℝ K) (hstrip : K ⊆ unitStrip) :
    IsDownwardCap (upperCap K) where
  nonempty := hne.mono (subset_upperCap (fun p hp => (hstrip hp).1))
  isCompact := isCompact_upperCap hcompact (fun p hp => (hstrip hp).1)
  convex := convex_upperCap hconvex
  inStrip := upperCap_subset_unitStrip hstrip
  downward := fun _ hp _ hy0 hyp => upperCap_downward hp hy0 hyp

theorem isCompact_horizontalProjection {K : Set Plane} (hK : IsCompact K) :
    IsCompact (horizontalProjection K) :=
  hK.image continuous_fst

theorem convex_horizontalProjection {K : Set Plane} (hK : Convex ℝ K) :
    Convex ℝ (horizontalProjection K) := by
  rintro x ⟨p, hp, rfl⟩ y ⟨q, hq, rfl⟩ a b ha hb hab
  exact ⟨a • p + b • q, hK hp hq ha hb hab, rfl⟩

def horizontalLeft (K : Set Plane) : ℝ := sInf (horizontalProjection K)

def horizontalRight (K : Set Plane) : ℝ := sSup (horizontalProjection K)

/-- A nonempty compact convex set has its exact horizontal projection interval. -/
theorem horizontalProjection_eq_Icc {K : Set Plane} (hne : K.Nonempty)
    (hcompact : IsCompact K) (hconvex : Convex ℝ K) :
    horizontalProjection K = Icc (horizontalLeft K) (horizontalRight K) :=
  eq_Icc_of_connected_compact
    ((convex_horizontalProjection hconvex).isConnected (hne.image Prod.fst))
    (isCompact_horizontalProjection hcompact)

theorem horizontalLeft_mem {K : Set Plane} (hne : K.Nonempty) (hK : IsCompact K) :
    horizontalLeft K ∈ horizontalProjection K :=
  (isCompact_horizontalProjection hK).sInf_mem (hne.image Prod.fst)

theorem horizontalRight_mem {K : Set Plane} (hne : K.Nonempty) (hK : IsCompact K) :
    horizontalRight K ∈ horizontalProjection K :=
  (isCompact_horizontalProjection hK).sSup_mem (hne.image Prod.fst)

theorem horizontalLeft_le_horizontalRight {K : Set Plane} (hne : K.Nonempty)
    (hK : IsCompact K) : horizontalLeft K ≤ horizontalRight K :=
  le_csSup (isCompact_horizontalProjection hK).bddAbove (horizontalLeft_mem hne hK)

/-- The exact vertical fiber, including any endpoint points. -/
def verticalFiber (K : Set Plane) (x : ℝ) : Set ℝ := {y | (x, y) ∈ K}

theorem verticalFiber_nonempty_iff {K : Set Plane} {x : ℝ} :
    (verticalFiber K x).Nonempty ↔ x ∈ horizontalProjection K := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨(x, y), hy, rfl⟩
  · rintro ⟨p, hp, hpx⟩
    refine ⟨p.2, ?_⟩
    change (x, p.2) ∈ K
    rw [← hpx]
    simpa only [Prod.mk.eta] using hp

theorem verticalFiber_eq_image (K : Set Plane) (x : ℝ) :
    verticalFiber K x = Prod.snd '' (K ∩ {p : Plane | p.1 = x}) := by
  apply Set.Subset.antisymm
  · intro y hy
    exact ⟨(x, y), ⟨hy, rfl⟩, rfl⟩
  · rintro y ⟨p, ⟨hp, hpx⟩, hpy⟩
    change (x, y) ∈ K
    have heq : p = (x, y) := Prod.ext hpx hpy
    simpa only [heq] using hp

theorem isCompact_verticalFiber {K : Set Plane} (hK : IsCompact K) (x : ℝ) :
    IsCompact (verticalFiber K x) := by
  rw [verticalFiber_eq_image]
  exact (hK.inter_right (isClosed_eq continuous_fst continuous_const)).image continuous_snd

/-- The attained fiber maximum, extended by zero off the horizontal projection. -/
def capRoof (K : Set Plane) (x : ℝ) : ℝ := by
  classical
  exact if x ∈ horizontalProjection K then sSup (verticalFiber K x) else 0

theorem capRoof_eq_zero_of_not_mem {K : Set Plane} {x : ℝ}
    (hx : x ∉ horizontalProjection K) : capRoof K x = 0 := by
  simp only [capRoof, if_neg hx]

/-- The roof is a point of the original compact fiber, rather than a limiting proxy. -/
theorem capRoof_mem {K : Set Plane} (hK : IsCompact K) {x : ℝ}
    (hx : x ∈ horizontalProjection K) : (x, capRoof K x) ∈ K := by
  have hmax := (isCompact_verticalFiber hK x).sSup_mem
    (verticalFiber_nonempty_iff.mpr hx)
  simpa only [capRoof, if_pos hx, verticalFiber, Set.mem_setOf_eq] using hmax

theorem le_capRoof {K : Set Plane} (hK : IsCompact K) {x y : ℝ}
    (hxy : (x, y) ∈ K) : y ≤ capRoof K x := by
  have hx : x ∈ horizontalProjection K := ⟨(x, y), hxy, rfl⟩
  have hle : y ≤ sSup (verticalFiber K x) :=
    le_csSup (isCompact_verticalFiber hK x).bddAbove hxy
  simpa only [capRoof, if_pos hx] using hle

theorem capRoof_nonneg {K : Set Plane} (hK : IsCompact K)
    (hK0 : ∀ p ∈ K, 0 ≤ p.2) (x : ℝ) : 0 ≤ capRoof K x := by
  by_cases hx : x ∈ horizontalProjection K
  · exact hK0 (x, capRoof K x) (capRoof_mem hK hx)
  · rw [capRoof_eq_zero_of_not_mem hx]

theorem capRoof_le_one {K : Set Plane} (hK : IsCompact K) (hstrip : K ⊆ unitStrip)
    (x : ℝ) : capRoof K x ≤ 1 := by
  by_cases hx : x ∈ horizontalProjection K
  · exact (hstrip (capRoof_mem hK hx)).2
  · rw [capRoof_eq_zero_of_not_mem hx]
    exact zero_le_one

/-- The original vertical fibers of a cap are exactly the closed roof intervals. -/
theorem IsDownwardCap.verticalFiber_eq_Icc {U : Set Plane} (hU : IsDownwardCap U)
    {x : ℝ} (hx : x ∈ horizontalProjection U) :
    verticalFiber U x = Icc 0 (capRoof U x) := by
  ext y
  constructor
  · intro hy
    exact ⟨(hU.inStrip hy).1, le_capRoof hU.isCompact hy⟩
  · rintro ⟨hy0, hyroof⟩
    exact hU.downward (x, capRoof U x) (capRoof_mem hU.isCompact hx) y hy0 hyroof

/-- Convexity of the actual cap gives concavity of its attained roof. -/
theorem IsDownwardCap.concaveOn_capRoof {U : Set Plane} (hU : IsDownwardCap U) :
    ConcaveOn ℝ (horizontalProjection U) (capRoof U) := by
  refine ⟨convex_horizontalProjection hU.convex, ?_⟩
  intro x hx y hy a b ha hb hab
  change a * capRoof U x + b * capRoof U y ≤ capRoof U (a * x + b * y)
  apply le_capRoof hU.isCompact
  simpa [smul_eq_mul] using hU.convex (capRoof_mem hU.isCompact hx) (capRoof_mem hU.isCompact hy)
    ha hb hab

/-- Both the projection and the roof are needed when zero-height fibers occur. -/
theorem IsDownwardCap.mem_iff_projection_and_roof {U : Set Plane}
    (hU : IsDownwardCap U) (p : Plane) :
    p ∈ U ↔ p.1 ∈ horizontalProjection U ∧ 0 ≤ p.2 ∧ p.2 ≤ capRoof U p.1 := by
  constructor
  · intro hp
    refine ⟨⟨p, hp, rfl⟩, (hU.inStrip hp).1, ?_⟩
    apply le_capRoof hU.isCompact
    simpa only [Prod.mk.eta] using hp
  · rintro ⟨hx, hy0, hyroof⟩
    have hp : (p.1, p.2) ∈ U := hU.downward (p.1, capRoof U p.1)
      (capRoof_mem hU.isCompact hx) p.2 hy0 hyroof
    simpa only [Prod.mk.eta] using hp

/-- This set equality retains all baseline and boundary points. -/
theorem IsDownwardCap.eq_of_projection_eq_of_capRoof_eq {U V : Set Plane}
    (hU : IsDownwardCap U) (hV : IsDownwardCap V)
    (hprojection : horizontalProjection U = horizontalProjection V)
    (hroof : capRoof U = capRoof V) : U = V := by
  ext p
  rw [hU.mem_iff_projection_and_roof, hV.mem_iff_projection_and_roof, hprojection, hroof]

/-- Downward filling preserves the actual attained roof at every abscissa. -/
theorem capRoof_upperCap {K : Set Plane} (hK : IsCompact K)
    (hK0 : ∀ p ∈ K, 0 ≤ p.2) (x : ℝ) : capRoof (upperCap K) x = capRoof K x := by
  have hcompact := isCompact_upperCap hK hK0
  by_cases hx : x ∈ horizontalProjection K
  · have hxcap : x ∈ horizontalProjection (upperCap K) := by
      rw [horizontalProjection_upperCap hK0]
      exact hx
    apply le_antisymm
    · obtain ⟨_, y, hroofy, hy⟩ := capRoof_mem hcompact hxcap
      exact hroofy.trans (le_capRoof hK hy)
    · exact le_capRoof hcompact (subset_upperCap hK0 (capRoof_mem hK hx))
  · have hxcap : x ∉ horizontalProjection (upperCap K) := by
      rw [horizontalProjection_upperCap hK0]
      exact hx
    rw [capRoof_eq_zero_of_not_mem hxcap, capRoof_eq_zero_of_not_mem hx]

/-- Positive-dimensional caps with interior are regular closed as actual sets. -/
theorem IsDownwardCap.closure_interior_eq {U : Set Plane} (hU : IsDownwardCap U)
    (hinterior : (interior U).Nonempty) : closure (interior U) = U := by
  rw [hU.convex.closure_interior_eq_closure_of_nonempty_interior hinterior,
    hU.isCompact.isClosed.closure_eq]

/-- Positive superlevels of the roof are projections of actual closed cap slices. -/
theorem capRoof_superlevel_eq_projection {K : Set Plane} (hK : IsCompact K)
    {c : ℝ} (hc : 0 < c) :
    {x | c ≤ capRoof K x} = horizontalProjection (K ∩ {p : Plane | c ≤ p.2}) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxproj : x ∈ horizontalProjection K := by
      by_contra hnot
      have hz := capRoof_eq_zero_of_not_mem hnot
      have hx' : c ≤ capRoof K x := hx
      have hcle : c ≤ 0 := by simpa only [hz] using hx'
      exact (not_le_of_gt hc) hcle
    exact ⟨(x, capRoof K x), ⟨capRoof_mem hK hxproj, hx⟩, rfl⟩
  · rintro x ⟨p, ⟨hp, hcp⟩, hpx⟩
    have hp' : (x, p.2) ∈ K := by
      rw [← hpx]
      simpa only [Prod.mk.eta] using hp
    exact hcp.trans (le_capRoof hK hp')

/-- Zero extension is upper semicontinuous even at projection endpoints. -/
theorem upperSemicontinuous_capRoof {K : Set Plane} (hK : IsCompact K)
    (hK0 : ∀ p ∈ K, 0 ≤ p.2) : UpperSemicontinuous (capRoof K) := by
  apply upperSemicontinuous_iff_isClosed_preimage.mpr
  intro c
  by_cases hc : c ≤ 0
  · have hfull : capRoof K ⁻¹' Ici c = (Set.univ : Set ℝ) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_univ, iff_true]
      exact hc.trans (capRoof_nonneg hK hK0 x)
    rw [hfull]
    exact isClosed_univ
  · change IsClosed {x | c ≤ capRoof K x}
    rw [capRoof_superlevel_eq_projection hK (lt_of_not_ge hc)]
    exact (isCompact_horizontalProjection
      (hK.inter_right (isClosed_le continuous_const continuous_snd))).isClosed

theorem measurable_capRoof {K : Set Plane} (hK : IsCompact K)
    (hK0 : ∀ p ∈ K, 0 ≤ p.2) : Measurable (capRoof K) :=
  (upperSemicontinuous_capRoof hK hK0).measurable

theorem IsDownwardCap.upperSemicontinuous_capRoof {U : Set Plane}
    (hU : IsDownwardCap U) : UpperSemicontinuous (capRoof U) :=
  AmbidextrousSofa.upperSemicontinuous_capRoof hU.isCompact (fun p hp => (hU.inStrip hp).1)

theorem IsDownwardCap.measurable_capRoof {U : Set Plane} (hU : IsDownwardCap U) :
    Measurable (capRoof U) :=
  hU.upperSemicontinuous_capRoof.measurable

theorem IsDownwardCap.measurableSet {U : Set Plane} (hU : IsDownwardCap U) :
    MeasurableSet U :=
  hU.isCompact.isClosed.measurableSet

end AmbidextrousSofa
