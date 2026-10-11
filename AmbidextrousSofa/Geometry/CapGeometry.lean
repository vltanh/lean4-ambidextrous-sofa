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

theorem actualHull_subset_unitStrip {S : Set Plane} (hS : S ⊆ unitStrip) :
    actualHull S ⊆ unitStrip :=
  convexHull_min hS ((convex_Icc (0 : ℝ) 1).linear_preimage (LinearMap.snd ℝ ℝ ℝ))

theorem actualHull_nonempty {S : Set Plane} (hS : S.Nonempty) :
    (actualHull S).Nonempty :=
  hS.mono (subset_actualHull S)

/-- Compactness is proved for the actual downward-filled set. -/
theorem isCompact_upperCap {K : Set Plane} (hK : IsCompact K)
    (hK0 : ∀ p ∈ K, 0 ≤ p.2) : IsCompact (upperCap K) := by
  -- downward filling is parametrized by vertical contraction to the baseline
  have h : upperCap K = (fun z : Plane × ℝ => (z.1.1, z.2 * z.1.2)) '' (K ×ˢ Icc (0 : ℝ) 1) := by
    refine Subset.antisymm ?_ ?_
    · rintro p ⟨hp0, y, hpy, hy⟩
      exact ⟨((p.1, y), p.2 / y), ⟨hy, div_nonneg hp0 (hp0.trans hpy),
        div_le_one_of_le₀ hpy (hp0.trans hpy)⟩,
        Prod.ext rfl (div_mul_cancel_of_imp fun h => le_antisymm (h ▸ hpy) hp0)⟩
    · rintro _ ⟨⟨q, t⟩, ⟨hq, ht⟩, rfl⟩
      exact ⟨mul_nonneg ht.1 (hK0 q hq), q.2, mul_le_of_le_one_left (hK0 q hq) ht.2, hq⟩
  rw [h]
  exact (hK.prod isCompact_Icc).image (by fun_prop)

/-- Every nonempty compact convex hull in the strip produces an intrinsic cap. -/
theorem isDownwardCap_upperCap {K : Set Plane} (hne : K.Nonempty)
    (hcompact : IsCompact K) (hconvex : Convex ℝ K) (hstrip : K ⊆ unitStrip) :
    IsDownwardCap (upperCap K) where
  nonempty := hne.mono (subset_upperCap (fun _ hp => (hstrip hp).1))
  isCompact := isCompact_upperCap hcompact (fun _ hp => (hstrip hp).1)
  convex := by
    rintro p ⟨hp0, yp, hpyp, hyp⟩ q ⟨hq0, yq, hqyq, hyq⟩ a b ha hb hab
    exact ⟨add_nonneg (mul_nonneg ha hp0) (mul_nonneg hb hq0), a * yp + b * yq,
      add_le_add (mul_le_mul_of_nonneg_left hpyp ha) (mul_le_mul_of_nonneg_left hqyq hb),
      by simpa [smul_eq_mul] using hconvex hyp hyq ha hb hab⟩
  inStrip := fun _ ⟨hp0, _, hpy, hy⟩ => ⟨hp0, hpy.trans (hstrip hy).2⟩
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

/-- A compact connected set has its exact horizontal projection interval. -/
theorem horizontalProjection_eq_Icc_of_isConnected {S : Set Plane}
    (hcompact : IsCompact S) (hconnected : IsConnected S) :
    horizontalProjection S = Icc (horizontalLeft S) (horizontalRight S) :=
  eq_Icc_of_connected_compact (hconnected.image Prod.fst continuous_fst.continuousOn)
    (isCompact_horizontalProjection hcompact)

/-- A cap has its exact horizontal projection interval. -/
theorem IsDownwardCap.horizontalProjection_eq_Icc {U : Set Plane} (hU : IsDownwardCap U) :
    horizontalProjection U = Icc (horizontalLeft U) (horizontalRight U) :=
  horizontalProjection_eq_Icc_of_isConnected hU.isCompact (hU.convex.isConnected hU.nonempty)

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
    (verticalFiber K x).Nonempty ↔ x ∈ horizontalProjection K :=
  ⟨fun ⟨y, hy⟩ => ⟨(x, y), hy, rfl⟩, by rintro ⟨p, hp, rfl⟩; exact ⟨p.2, hp⟩⟩

theorem isCompact_verticalFiber {K : Set Plane} (hK : IsCompact K) (x : ℝ) :
    IsCompact (verticalFiber K x) := by
  convert (hK.inter_right (isClosed_eq continuous_fst continuous_const)).image continuous_snd
  ext y
  exact ⟨fun hy => ⟨(x, y), ⟨hy, rfl⟩, rfl⟩, by rintro ⟨p, ⟨hp, rfl⟩, rfl⟩; exact hp⟩

/-- The attained fiber maximum, extended by zero off the horizontal projection. -/
def capRoof (K : Set Plane) (x : ℝ) : ℝ := by
  classical
  exact if x ∈ horizontalProjection K then sSup (verticalFiber K x) else 0

theorem capRoof_eq_zero_of_not_mem {K : Set Plane} {x : ℝ}
    (hx : x ∉ horizontalProjection K) : capRoof K x = 0 := by
  simp only [capRoof, hx, ↓reduceIte]

/-- The roof is a point of the original compact fiber, rather than a limiting proxy. -/
theorem capRoof_mem {K : Set Plane} (hK : IsCompact K) {x : ℝ}
    (hx : x ∈ horizontalProjection K) : (x, capRoof K x) ∈ K := by
  simpa only [capRoof, hx, ↓reduceIte, verticalFiber, Set.mem_ofPred_eq] using
    (isCompact_verticalFiber hK x).sSup_mem (verticalFiber_nonempty_iff.mpr hx)

theorem le_capRoof {K : Set Plane} (hK : IsCompact K) {x y : ℝ}
    (hxy : (x, y) ∈ K) : y ≤ capRoof K x := by
  simpa only [capRoof, show x ∈ horizontalProjection K from ⟨(x, y), hxy, rfl⟩, ↓reduceIte] using
    le_csSup (isCompact_verticalFiber hK x).bddAbove hxy

theorem capRoof_nonneg {K : Set Plane} (hK : IsCompact K)
    (hK0 : ∀ p ∈ K, 0 ≤ p.2) (x : ℝ) : 0 ≤ capRoof K x := by
  by_cases hx : x ∈ horizontalProjection K
  exacts [hK0 _ (capRoof_mem hK hx), (capRoof_eq_zero_of_not_mem hx).ge]

theorem capRoof_le_one {K : Set Plane} (hK : IsCompact K) (hstrip : K ⊆ unitStrip)
    (x : ℝ) : capRoof K x ≤ 1 := by
  by_cases hx : x ∈ horizontalProjection K
  exacts [(hstrip (capRoof_mem hK hx)).2, (capRoof_eq_zero_of_not_mem hx).trans_le zero_le_one]

/-- The original vertical fibers of a cap are exactly the closed roof intervals. -/
theorem IsDownwardCap.verticalFiber_eq_Icc {U : Set Plane} (hU : IsDownwardCap U)
    {x : ℝ} (hx : x ∈ horizontalProjection U) :
    verticalFiber U x = Icc 0 (capRoof U x) :=
  Set.ext fun y => ⟨fun hy => ⟨(hU.inStrip hy).1, le_capRoof hU.isCompact hy⟩,
    fun ⟨hy0, hyroof⟩ => hU.downward _ (capRoof_mem hU.isCompact hx) y hy0 hyroof⟩

/-- Convexity of the actual cap gives concavity of its attained roof. -/
theorem IsDownwardCap.concaveOn_capRoof {U : Set Plane} (hU : IsDownwardCap U) :
    ConcaveOn ℝ (horizontalProjection U) (capRoof U) := by
  refine ⟨convex_horizontalProjection hU.convex, fun x hx y hy a b ha hb hab =>
    le_capRoof hU.isCompact ?_⟩
  simpa [smul_eq_mul] using hU.convex (capRoof_mem hU.isCompact hx) (capRoof_mem hU.isCompact hy)
    ha hb hab

/-- Both the projection and the roof are needed when zero-height fibers occur. -/
theorem IsDownwardCap.mem_iff_projection_and_roof {U : Set Plane}
    (hU : IsDownwardCap U) (p : Plane) :
    p ∈ U ↔ p.1 ∈ horizontalProjection U ∧ 0 ≤ p.2 ∧ p.2 ≤ capRoof U p.1 :=
  ⟨fun hp => ⟨⟨p, hp, rfl⟩, (hU.inStrip hp).1, le_capRoof hU.isCompact hp⟩,
    fun ⟨hx, hy0, hyroof⟩ => hU.downward _ (capRoof_mem hU.isCompact hx) p.2 hy0 hyroof⟩

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
  · obtain ⟨_, y, hroofy, hy⟩ :=
      capRoof_mem hcompact (by rwa [horizontalProjection_upperCap hK0] : x ∈ _)
    exact le_antisymm (hroofy.trans (le_capRoof hK hy))
      (le_capRoof hcompact (subset_upperCap hK0 (capRoof_mem hK hx)))
  · rw [capRoof_eq_zero_of_not_mem hx,
      capRoof_eq_zero_of_not_mem (by rwa [horizontalProjection_upperCap hK0])]

/-- Zero extension is upper semicontinuous even at projection endpoints. -/
theorem upperSemicontinuous_capRoof {K : Set Plane} (hK : IsCompact K)
    (hK0 : ∀ p ∈ K, 0 ≤ p.2) : UpperSemicontinuous (capRoof K) := by
  refine upperSemicontinuous_iff_isClosed_preimage.mpr fun c => ?_
  by_cases hc : c ≤ 0
  · convert isClosed_univ
    exact eq_univ_of_forall fun x => hc.trans (capRoof_nonneg hK hK0 x)
  -- positive superlevels of the roof are projections of actual closed cap slices
  convert (isCompact_horizontalProjection
    (hK.inter_right (isClosed_le continuous_const continuous_snd))).isClosed
  refine Subset.antisymm (fun x hx => ?_) ?_
  · have hxK : x ∈ horizontalProjection K := by
      by_contra h
      exact hc (capRoof_eq_zero_of_not_mem h ▸ hx)
    exact ⟨_, ⟨capRoof_mem hK hxK, hx⟩, rfl⟩
  · rintro _ ⟨p, ⟨hp, hcp⟩, rfl⟩
    exact hcp.trans (le_capRoof hK hp)

theorem measurable_capRoof {K : Set Plane} (hK : IsCompact K)
    (hK0 : ∀ p ∈ K, 0 ≤ p.2) : Measurable (capRoof K) :=
  (upperSemicontinuous_capRoof hK hK0).measurable

theorem IsDownwardCap.upperSemicontinuous_capRoof {U : Set Plane}
    (hU : IsDownwardCap U) : UpperSemicontinuous (capRoof U) :=
  AmbidextrousSofa.upperSemicontinuous_capRoof hU.isCompact (fun _ hp => (hU.inStrip hp).1)

theorem IsDownwardCap.measurable_capRoof {U : Set Plane} (hU : IsDownwardCap U) :
    Measurable (capRoof U) :=
  hU.upperSemicontinuous_capRoof.measurable

end AmbidextrousSofa
