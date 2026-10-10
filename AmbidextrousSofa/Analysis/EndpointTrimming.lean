module

public import AmbidextrousSofa.Analysis.CapTranslation
public import AmbidextrousSofa.Analysis.CapCompactness
public import AmbidextrousSofa.Analysis.CapOrder

@[expose] public section

/-!
# Actual inward cuts and horizontal erosions

Both constructions remain in the complete downward-cap domain. Their
projections are the actual shortened intervals, even if an old endpoint
face has height zero. A cut retains the old roof. A horizontal erosion has
the minimum of the two translated roofs and tightens supports by at least
the positive horizontal component of the translation.

The distance estimate uses the product metric on `Plane`. Contracting a
point toward one baseline endpoint gives a point in the erosion; its
translate is the contraction toward the other endpoint. Thus, for width
`W > 0`, both erosion and trimming have Hausdorff distance at most
`(ε / W) * max W 1`. In particular the bound is `ε` when `W ≥ 1`.
No positive endpoint face, positive top face, or differentiability of the
roof is required.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem IsDownwardCap.fst_mem_Icc {U : Set Plane} (hU : IsDownwardCap U)
    {p : Plane} (hp : p ∈ U) :
    p.1 ∈ Icc (horizontalLeft U) (horizontalRight U) := by
  rw [← horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
  exact ⟨p, hp, rfl⟩

theorem IsDownwardCap.baseline_mem_of_mem_projection {U : Set Plane}
    (hU : IsDownwardCap U) {x : ℝ} (hx : x ∈ horizontalProjection U) :
    (x, 0) ∈ U :=
  hU.baseline_mem (capRoof_mem hU.isCompact hx)

theorem IsDownwardCap.inter {U V : Set Plane} (hU : IsDownwardCap U)
    (hV : IsDownwardCap V) (hne : (U ∩ V).Nonempty) :
    IsDownwardCap (U ∩ V) where
  nonempty := hne
  isCompact := hU.isCompact.inter_right hV.isCompact.isClosed
  convex := hU.convex.inter hV.convex
  inStrip := fun _ hp => hU.inStrip hp.1
  downward := fun p hp y hy0 hyp =>
    ⟨hU.downward p hp.1 y hy0 hyp, hV.downward p hp.2 y hy0 hyp⟩

/-- Retain a closed interval of actual vertical sections. -/
def horizontalCut (U : Set Plane) (a b : ℝ) : Set Plane :=
  {p | p ∈ U ∧ p.1 ∈ Icc a b}

theorem horizontalCut_subset (U : Set Plane) (a b : ℝ) :
    horizontalCut U a b ⊆ U := fun _ hp => hp.1

theorem IsDownwardCap.horizontalCut {U : Set Plane} (hU : IsDownwardCap U)
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ horizontalProjection U) :
    IsDownwardCap (AmbidextrousSofa.horizontalCut U a b) := by
  refine ⟨?_, ?_, ?_, fun _ hp => hU.inStrip hp.1, ?_⟩
  · exact ⟨(a, 0), hU.baseline_mem_of_mem_projection (hsub ⟨le_rfl, hab⟩),
      le_rfl, hab⟩
  · change IsCompact (U ∩ (Prod.fst ⁻¹' Icc a b))
    exact hU.isCompact.inter_right (isClosed_Icc.preimage continuous_fst)
  · intro p hp q hq c d hc hd hcd
    refine ⟨hU.convex hp.1 hq.1 hc hd hcd, ?_⟩
    change c * p.1 + d * q.1 ∈ Icc a b
    simpa only [smul_eq_mul] using (convex_Icc a b) hp.2 hq.2 hc hd hcd
  · intro p hp y hy0 hyp
    exact ⟨hU.downward p hp.1 y hy0 hyp, hp.2⟩

theorem horizontalProjection_horizontalCut {U : Set Plane} (hU : IsDownwardCap U)
    {a b : ℝ} (hsub : Icc a b ⊆ horizontalProjection U) :
    horizontalProjection (horizontalCut U a b) = Icc a b := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp.2
  · intro hx
    exact ⟨(x, 0), ⟨hU.baseline_mem_of_mem_projection (hsub hx), hx⟩, rfl⟩

theorem horizontalLeft_horizontalCut {U : Set Plane} (hU : IsDownwardCap U)
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ horizontalProjection U) :
    horizontalLeft (horizontalCut U a b) = a := by
  rw [horizontalLeft, horizontalProjection_horizontalCut hU hsub, csInf_Icc hab]

theorem horizontalRight_horizontalCut {U : Set Plane} (hU : IsDownwardCap U)
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ horizontalProjection U) :
    horizontalRight (horizontalCut U a b) = b := by
  rw [horizontalRight, horizontalProjection_horizontalCut hU hsub, csSup_Icc hab]

theorem capRoof_horizontalCut {U : Set Plane} (hU : IsDownwardCap U)
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ horizontalProjection U)
    {x : ℝ} (hx : x ∈ Icc a b) :
    capRoof (horizontalCut U a b) x = capRoof U x := by
  have hC := hU.horizontalCut hab hsub
  have hxC : x ∈ horizontalProjection (horizontalCut U a b) := by
    rw [horizontalProjection_horizontalCut hU hsub]
    exact hx
  apply le_antisymm
  · exact le_capRoof hU.isCompact (capRoof_mem hC.isCompact hxC).1
  · exact le_capRoof hC.isCompact ⟨capRoof_mem hU.isCompact (hsub hx), hx⟩

/-- An inward right cut uses the original actual projection endpoint. -/
def rightTrim (U : Set Plane) (ε : ℝ) : Set Plane :=
  horizontalCut U (horizontalLeft U) (horizontalRight U - ε)

def leftTrim (U : Set Plane) (ε : ℝ) : Set Plane :=
  horizontalCut U (horizontalLeft U + ε) (horizontalRight U)

theorem mem_rightTrim_iff {U : Set Plane} (hU : IsDownwardCap U) (ε : ℝ) (p : Plane) :
    p ∈ rightTrim U ε ↔ p ∈ U ∧ p.1 ≤ horizontalRight U - ε := by
  constructor
  · intro hp
    exact ⟨hp.1, hp.2.2⟩
  · rintro ⟨hp, hx⟩
    exact ⟨hp, (hU.fst_mem_Icc hp).1, hx⟩

theorem mem_leftTrim_iff {U : Set Plane} (hU : IsDownwardCap U) (ε : ℝ) (p : Plane) :
    p ∈ leftTrim U ε ↔ p ∈ U ∧ horizontalLeft U + ε ≤ p.1 := by
  constructor
  · intro hp
    exact ⟨hp.1, hp.2.1⟩
  · rintro ⟨hp, hx⟩
    exact ⟨hp, hx, (hU.fst_mem_Icc hp).2⟩

theorem rightTrim_subset (U : Set Plane) (ε : ℝ) : rightTrim U ε ⊆ U :=
  horizontalCut_subset U _ _

theorem leftTrim_subset (U : Set Plane) (ε : ℝ) : leftTrim U ε ⊆ U :=
  horizontalCut_subset U _ _

theorem rightTrim_interval_subset {U : Set Plane} (hU : IsDownwardCap U)
    {ε : ℝ} (hε : 0 ≤ ε) :
    Icc (horizontalLeft U) (horizontalRight U - ε) ⊆ horizontalProjection U := by
  rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
  intro x hx
  exact ⟨hx.1, hx.2.trans (sub_le_self _ hε)⟩

theorem leftTrim_interval_subset {U : Set Plane} (hU : IsDownwardCap U)
    {ε : ℝ} (hε : 0 ≤ ε) :
    Icc (horizontalLeft U + ε) (horizontalRight U) ⊆ horizontalProjection U := by
  rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
  intro x hx
  exact ⟨(le_add_of_nonneg_right hε).trans hx.1, hx.2⟩

theorem IsDownwardCap.rightTrim {U : Set Plane} (hU : IsDownwardCap U)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) : IsDownwardCap (AmbidextrousSofa.rightTrim U ε) :=
  hU.horizontalCut (by unfold capWidth at hεW; linarith) (rightTrim_interval_subset hU hε0)

theorem IsDownwardCap.leftTrim {U : Set Plane} (hU : IsDownwardCap U)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) : IsDownwardCap (AmbidextrousSofa.leftTrim U ε) :=
  hU.horizontalCut (by unfold capWidth at hεW; linarith) (leftTrim_interval_subset hU hε0)

theorem horizontalLeft_rightTrim {U : Set Plane} (hU : IsDownwardCap U)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) :
    horizontalLeft (rightTrim U ε) = horizontalLeft U :=
  horizontalLeft_horizontalCut hU (by unfold capWidth at hεW; linarith)
    (rightTrim_interval_subset hU hε0)

theorem horizontalRight_rightTrim {U : Set Plane} (hU : IsDownwardCap U)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) :
    horizontalRight (rightTrim U ε) = horizontalRight U - ε :=
  horizontalRight_horizontalCut hU (by unfold capWidth at hεW; linarith)
    (rightTrim_interval_subset hU hε0)

theorem horizontalLeft_leftTrim {U : Set Plane} (hU : IsDownwardCap U)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) :
    horizontalLeft (leftTrim U ε) = horizontalLeft U + ε :=
  horizontalLeft_horizontalCut hU (by unfold capWidth at hεW; linarith)
    (leftTrim_interval_subset hU hε0)

theorem horizontalRight_leftTrim {U : Set Plane} (hU : IsDownwardCap U)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) :
    horizontalRight (leftTrim U ε) = horizontalRight U :=
  horizontalRight_horizontalCut hU (by unfold capWidth at hεW; linarith)
    (leftTrim_interval_subset hU hε0)

theorem capRoof_rightTrim {U : Set Plane} (hU : IsDownwardCap U)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) {x : ℝ}
    (hx : x ∈ Icc (horizontalLeft U) (horizontalRight U - ε)) :
    capRoof (rightTrim U ε) x = capRoof U x :=
  capRoof_horizontalCut hU (by unfold capWidth at hεW; linarith)
    (rightTrim_interval_subset hU hε0) hx

theorem capRoof_leftTrim {U : Set Plane} (hU : IsDownwardCap U)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) {x : ℝ}
    (hx : x ∈ Icc (horizontalLeft U + ε) (horizontalRight U)) :
    capRoof (leftTrim U ε) x = capRoof U x :=
  capRoof_horizontalCut hU (by unfold capWidth at hεW; linarith)
    (leftTrim_interval_subset hU hε0) hx

/-- A point survives precisely when its right translate is also in the cap. -/
def rightErosion (U : Set Plane) (ε : ℝ) : Set Plane :=
  {p | p ∈ U ∧ (p.1 + ε, p.2) ∈ U}

def leftErosion (U : Set Plane) (ε : ℝ) : Set Plane :=
  {p | p ∈ U ∧ (p.1 - ε, p.2) ∈ U}

theorem rightErosion_eq_inter_horizontalTranslate (U : Set Plane) (ε : ℝ) :
    rightErosion U ε = U ∩ horizontalTranslate U (-ε) := by
  ext p
  rw [mem_inter_iff, mem_horizontalTranslate_iff]
  simp only [rightErosion, mem_setOf_eq, sub_neg_eq_add]

theorem leftErosion_eq_inter_horizontalTranslate (U : Set Plane) (ε : ℝ) :
    leftErosion U ε = U ∩ horizontalTranslate U ε := by
  ext p
  rw [mem_inter_iff, mem_horizontalTranslate_iff]
  rfl

theorem rightErosion_subset (U : Set Plane) (ε : ℝ) : rightErosion U ε ⊆ U :=
  fun _ hp => hp.1

theorem leftErosion_subset (U : Set Plane) (ε : ℝ) : leftErosion U ε ⊆ U :=
  fun _ hp => hp.1

theorem rightErosion_subset_rightTrim {U : Set Plane} (hU : IsDownwardCap U) (ε : ℝ) :
    rightErosion U ε ⊆ rightTrim U ε := by
  intro p hp
  apply (mem_rightTrim_iff hU ε p).mpr
  have hx := (hU.fst_mem_Icc hp.2).2
  exact ⟨hp.1, by change p.1 + ε ≤ horizontalRight U at hx; linarith⟩

theorem leftErosion_subset_leftTrim {U : Set Plane} (hU : IsDownwardCap U) (ε : ℝ) :
    leftErosion U ε ⊆ leftTrim U ε := by
  intro p hp
  apply (mem_leftTrim_iff hU ε p).mpr
  have hx := (hU.fst_mem_Icc hp.2).1
  exact ⟨hp.1, by change horizontalLeft U ≤ p.1 - ε at hx; linarith⟩

theorem IsDownwardCap.rightErosion {U : Set Plane} (hU : IsDownwardCap U)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) :
    IsDownwardCap (AmbidextrousSofa.rightErosion U ε) := by
  rw [rightErosion_eq_inter_horizontalTranslate]
  apply hU.inter (hU.horizontalTranslate (-ε))
  refine ⟨(horizontalLeft U, 0),
    hU.baseline_mem_of_mem_projection (horizontalLeft_mem hU.nonempty hU.isCompact), ?_⟩
  rw [mem_horizontalTranslate_iff]
  simp only [sub_neg_eq_add]
  apply hU.baseline_mem_of_mem_projection
  rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
  unfold capWidth at hεW
  exact ⟨by linarith, by linarith⟩

theorem IsDownwardCap.leftErosion {U : Set Plane} (hU : IsDownwardCap U)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) :
    IsDownwardCap (AmbidextrousSofa.leftErosion U ε) := by
  rw [leftErosion_eq_inter_horizontalTranslate]
  apply hU.inter (hU.horizontalTranslate ε)
  refine ⟨(horizontalRight U, 0),
    hU.baseline_mem_of_mem_projection (horizontalRight_mem hU.nonempty hU.isCompact), ?_⟩
  rw [mem_horizontalTranslate_iff]
  apply hU.baseline_mem_of_mem_projection
  rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
  unfold capWidth at hεW
  exact ⟨by linarith, by linarith⟩

theorem horizontalProjection_rightErosion {U : Set Plane} (hU : IsDownwardCap U)
    {ε : ℝ} (hε0 : 0 ≤ ε) :
    horizontalProjection (rightErosion U ε) =
      Icc (horizontalLeft U) (horizontalRight U - ε) := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (rightErosion_subset_rightTrim hU ε hp).2
  · intro hx
    refine ⟨(x, 0), ⟨hU.baseline_mem_of_mem_projection
      (rightTrim_interval_subset hU hε0 hx), ?_⟩, rfl⟩
    apply hU.baseline_mem_of_mem_projection
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem horizontalProjection_leftErosion {U : Set Plane} (hU : IsDownwardCap U)
    {ε : ℝ} (hε0 : 0 ≤ ε) :
    horizontalProjection (leftErosion U ε) =
      Icc (horizontalLeft U + ε) (horizontalRight U) := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (leftErosion_subset_leftTrim hU ε hp).2
  · intro hx
    refine ⟨(x, 0), ⟨hU.baseline_mem_of_mem_projection
      (leftTrim_interval_subset hU hε0 hx), ?_⟩, rfl⟩
    apply hU.baseline_mem_of_mem_projection
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem horizontalLeft_rightErosion {U : Set Plane} (hU : IsDownwardCap U)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) :
    horizontalLeft (rightErosion U ε) = horizontalLeft U := by
  rw [horizontalLeft, horizontalProjection_rightErosion hU hε0,
    csInf_Icc (by unfold capWidth at hεW; linarith)]

theorem horizontalRight_rightErosion {U : Set Plane} (hU : IsDownwardCap U)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) :
    horizontalRight (rightErosion U ε) = horizontalRight U - ε := by
  rw [horizontalRight, horizontalProjection_rightErosion hU hε0,
    csSup_Icc (by unfold capWidth at hεW; linarith)]

theorem horizontalLeft_leftErosion {U : Set Plane} (hU : IsDownwardCap U)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) :
    horizontalLeft (leftErosion U ε) = horizontalLeft U + ε := by
  rw [horizontalLeft, horizontalProjection_leftErosion hU hε0,
    csInf_Icc (by unfold capWidth at hεW; linarith)]

theorem horizontalRight_leftErosion {U : Set Plane} (hU : IsDownwardCap U)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) :
    horizontalRight (leftErosion U ε) = horizontalRight U := by
  rw [horizontalRight, horizontalProjection_leftErosion hU hε0,
    csSup_Icc (by unfold capWidth at hεW; linarith)]

/-- Coordinate distance to a contraction toward any baseline point. -/
theorem dist_baseline_contraction_le {U : Set Plane} (hU : IsDownwardCap U)
    {p : Plane} (hp : p ∈ U) {a lam : ℝ}
    (ha : a ∈ Icc (horizontalLeft U) (horizontalRight U)) (hlam : 0 ≤ lam) :
    dist p ((1 - lam) • p + lam • (a, 0)) ≤ lam * max (capWidth U) 1 := by
  have hpx := hU.fst_mem_Icc hp
  have hpy := hU.inStrip hp
  have hx : |p.1 - a| ≤ capWidth U := by
    apply abs_le.mpr
    unfold capWidth
    exact ⟨by linarith [hpx.1, ha.2], by linarith [hpx.2, ha.1]⟩
  have hy : |p.2| ≤ 1 := by
    rw [abs_of_nonneg hpy.1]
    exact hpy.2
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  change max |p.1 - ((1 - lam) * p.1 + lam * a)|
    |p.2 - ((1 - lam) * p.2 + lam * 0)| ≤ lam * max (capWidth U) 1
  have hxf : p.1 - ((1 - lam) * p.1 + lam * a) = lam * (p.1 - a) := by ring
  have hyf : p.2 - ((1 - lam) * p.2 + lam * 0) = lam * p.2 := by ring
  rw [hxf, hyf, abs_mul, abs_mul, abs_of_nonneg hlam]
  exact max_le
    ((mul_le_mul_of_nonneg_left hx hlam).trans
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hlam))
    ((mul_le_mul_of_nonneg_left hy hlam).trans
      (mul_le_mul_of_nonneg_left (le_max_right _ _) hlam))

theorem exists_rightErosion_point_dist_le {U : Set Plane} (hU : IsDownwardCap U)
    (hW : 0 < capWidth U) {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U)
    {p : Plane} (hp : p ∈ U) :
    ∃ q ∈ rightErosion U ε,
      dist p q ≤ (ε / capWidth U) * max (capWidth U) 1 := by
  let lam := ε / capWidth U
  have hlam0 : 0 ≤ lam := div_nonneg hε0 hW.le
  have hlam1 : lam ≤ 1 := (div_le_one hW).mpr hεW
  have hlamW : lam * (horizontalRight U - horizontalLeft U) = ε := by
    change ε / capWidth U * capWidth U = ε
    exact div_mul_cancel₀ ε hW.ne'
  let q : Plane := (1 - lam) • p + lam • (horizontalLeft U, 0)
  have hleft := hU.baseline_mem_of_mem_projection
    (horizontalLeft_mem hU.nonempty hU.isCompact)
  have hright := hU.baseline_mem_of_mem_projection
    (horizontalRight_mem hU.nonempty hU.isCompact)
  have hq : q ∈ U := hU.convex hp hleft (sub_nonneg.mpr hlam1) hlam0 (by ring)
  have hshift : (q.1 + ε, q.2) =
      (1 - lam) • p + lam • (horizontalRight U, 0) := by
    apply Prod.ext
    · change (1 - lam) * p.1 + lam * horizontalLeft U + ε =
        (1 - lam) * p.1 + lam * horizontalRight U
      nlinarith [hlamW]
    · simp only [q, Prod.snd_add, Prod.smul_snd]
  refine ⟨q, ⟨hq, ?_⟩, ?_⟩
  · rw [hshift]
    exact hU.convex hp hright (sub_nonneg.mpr hlam1) hlam0 (by ring)
  · exact dist_baseline_contraction_le hU hp
      ⟨le_rfl, horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact⟩ hlam0

theorem exists_leftErosion_point_dist_le {U : Set Plane} (hU : IsDownwardCap U)
    (hW : 0 < capWidth U) {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U)
    {p : Plane} (hp : p ∈ U) :
    ∃ q ∈ leftErosion U ε,
      dist p q ≤ (ε / capWidth U) * max (capWidth U) 1 := by
  let lam := ε / capWidth U
  have hlam0 : 0 ≤ lam := div_nonneg hε0 hW.le
  have hlam1 : lam ≤ 1 := (div_le_one hW).mpr hεW
  have hlamW : lam * (horizontalRight U - horizontalLeft U) = ε := by
    change ε / capWidth U * capWidth U = ε
    exact div_mul_cancel₀ ε hW.ne'
  let q : Plane := (1 - lam) • p + lam • (horizontalRight U, 0)
  have hleft := hU.baseline_mem_of_mem_projection
    (horizontalLeft_mem hU.nonempty hU.isCompact)
  have hright := hU.baseline_mem_of_mem_projection
    (horizontalRight_mem hU.nonempty hU.isCompact)
  have hq : q ∈ U := hU.convex hp hright (sub_nonneg.mpr hlam1) hlam0 (by ring)
  have hshift : (q.1 - ε, q.2) =
      (1 - lam) • p + lam • (horizontalLeft U, 0) := by
    apply Prod.ext
    · change (1 - lam) * p.1 + lam * horizontalRight U - ε =
        (1 - lam) * p.1 + lam * horizontalLeft U
      nlinarith [hlamW]
    · simp only [q, Prod.snd_add, Prod.smul_snd]
  refine ⟨q, ⟨hq, ?_⟩, ?_⟩
  · rw [hshift]
    exact hU.convex hp hleft (sub_nonneg.mpr hlam1) hlam0 (by ring)
  · exact dist_baseline_contraction_le hU hp
      ⟨horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact, le_rfl⟩ hlam0

theorem hausdorffDist_rightErosion_le {U : Set Plane} (hU : IsDownwardCap U)
    (hW : 0 < capWidth U) {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) :
    Metric.hausdorffDist (rightErosion U ε) U ≤
      (ε / capWidth U) * max (capWidth U) 1 := by
  have hb : 0 ≤ (ε / capWidth U) * max (capWidth U) 1 :=
    mul_nonneg (div_nonneg hε0 hW.le) (zero_le_one.trans (le_max_right _ _))
  apply Metric.hausdorffDist_le_of_mem_dist hb
  · intro p hp
    exact ⟨p, hp.1, by simpa only [dist_self] using hb⟩
  · exact fun p hp => exists_rightErosion_point_dist_le hU hW hε0 hεW hp

theorem hausdorffDist_leftErosion_le {U : Set Plane} (hU : IsDownwardCap U)
    (hW : 0 < capWidth U) {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) :
    Metric.hausdorffDist (leftErosion U ε) U ≤
      (ε / capWidth U) * max (capWidth U) 1 := by
  have hb : 0 ≤ (ε / capWidth U) * max (capWidth U) 1 :=
    mul_nonneg (div_nonneg hε0 hW.le) (zero_le_one.trans (le_max_right _ _))
  apply Metric.hausdorffDist_le_of_mem_dist hb
  · intro p hp
    exact ⟨p, hp.1, by simpa only [dist_self] using hb⟩
  · exact fun p hp => exists_leftErosion_point_dist_le hU hW hε0 hεW hp

theorem hausdorffDist_rightTrim_le {U : Set Plane} (hU : IsDownwardCap U)
    (hW : 0 < capWidth U) {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) :
    Metric.hausdorffDist (rightTrim U ε) U ≤
      (ε / capWidth U) * max (capWidth U) 1 := by
  have hb : 0 ≤ (ε / capWidth U) * max (capWidth U) 1 :=
    mul_nonneg (div_nonneg hε0 hW.le) (zero_le_one.trans (le_max_right _ _))
  apply Metric.hausdorffDist_le_of_mem_dist hb
  · intro p hp
    exact ⟨p, hp.1, by simpa only [dist_self] using hb⟩
  · intro p hp
    obtain ⟨q, hq, hd⟩ := exists_rightErosion_point_dist_le hU hW hε0 hεW hp
    exact ⟨q, rightErosion_subset_rightTrim hU ε hq, hd⟩

theorem hausdorffDist_leftTrim_le {U : Set Plane} (hU : IsDownwardCap U)
    (hW : 0 < capWidth U) {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) :
    Metric.hausdorffDist (leftTrim U ε) U ≤
      (ε / capWidth U) * max (capWidth U) 1 := by
  have hb : 0 ≤ (ε / capWidth U) * max (capWidth U) 1 :=
    mul_nonneg (div_nonneg hε0 hW.le) (zero_le_one.trans (le_max_right _ _))
  apply Metric.hausdorffDist_le_of_mem_dist hb
  · intro p hp
    exact ⟨p, hp.1, by simpa only [dist_self] using hb⟩
  · intro p hp
    obtain ⟨q, hq, hd⟩ := exists_leftErosion_point_dist_le hU hW hε0 hεW hp
    exact ⟨q, leftErosion_subset_leftTrim hU ε hq, hd⟩

theorem hausdorffDist_rightErosion_le_of_one_le_width {U : Set Plane}
    (hU : IsDownwardCap U) (hW : 1 ≤ capWidth U)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) :
    Metric.hausdorffDist (rightErosion U ε) U ≤ ε := by
  have hW0 : 0 < capWidth U := zero_lt_one.trans_le hW
  simpa only [max_eq_left hW, div_mul_cancel₀ ε hW0.ne'] using
    hausdorffDist_rightErosion_le hU hW0 hε0 hεW

theorem hausdorffDist_leftErosion_le_of_one_le_width {U : Set Plane}
    (hU : IsDownwardCap U) (hW : 1 ≤ capWidth U)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) :
    Metric.hausdorffDist (leftErosion U ε) U ≤ ε := by
  have hW0 : 0 < capWidth U := zero_lt_one.trans_le hW
  simpa only [max_eq_left hW, div_mul_cancel₀ ε hW0.ne'] using
    hausdorffDist_leftErosion_le hU hW0 hε0 hεW

theorem hausdorffDist_rightTrim_le_of_one_le_width {U : Set Plane}
    (hU : IsDownwardCap U) (hW : 1 ≤ capWidth U)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) :
    Metric.hausdorffDist (rightTrim U ε) U ≤ ε := by
  have hW0 : 0 < capWidth U := zero_lt_one.trans_le hW
  simpa only [max_eq_left hW, div_mul_cancel₀ ε hW0.ne'] using
    hausdorffDist_rightTrim_le hU hW0 hε0 hεW

theorem hausdorffDist_leftTrim_le_of_one_le_width {U : Set Plane}
    (hU : IsDownwardCap U) (hW : 1 ≤ capWidth U)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) :
    Metric.hausdorffDist (leftTrim U ε) U ≤ ε := by
  have hW0 : 0 < capWidth U := zero_lt_one.trans_le hW
  simpa only [max_eq_left hW, div_mul_cancel₀ ε hW0.ne'] using
    hausdorffDist_leftTrim_le hU hW0 hε0 hεW

theorem abs_support_rightTrim_sub_le {U : Set Plane} (hU : IsDownwardCap U)
    (hW : 1 ≤ capWidth U) {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U)
    (v : Plane) :
    |support (rightTrim U ε) v - support U v| ≤ ε * (|v.1| + |v.2|) := by
  have hT := hU.rightTrim hε0 hεW
  exact (abs_support_sub_le_hausdorff hT.isCompact hT.nonempty hU.isCompact hU.nonempty v).trans
    (mul_le_mul_of_nonneg_right (hausdorffDist_rightTrim_le_of_one_le_width hU hW hε0 hεW)
      (add_nonneg (abs_nonneg _) (abs_nonneg _)))

theorem abs_support_leftTrim_sub_le {U : Set Plane} (hU : IsDownwardCap U)
    (hW : 1 ≤ capWidth U) {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U)
    (v : Plane) :
    |support (leftTrim U ε) v - support U v| ≤ ε * (|v.1| + |v.2|) := by
  have hT := hU.leftTrim hε0 hεW
  exact (abs_support_sub_le_hausdorff hT.isCompact hT.nonempty hU.isCompact hU.nonempty v).trans
    (mul_le_mul_of_nonneg_right (hausdorffDist_leftTrim_le_of_one_le_width hU hW hε0 hεW)
      (add_nonneg (abs_nonneg _) (abs_nonneg _)))

theorem abs_support_rightErosion_sub_le {U : Set Plane} (hU : IsDownwardCap U)
    (hW : 1 ≤ capWidth U) {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U)
    (v : Plane) :
    |support (rightErosion U ε) v - support U v| ≤ ε * (|v.1| + |v.2|) := by
  have hE := hU.rightErosion hε0 hεW
  exact (abs_support_sub_le_hausdorff hE.isCompact hE.nonempty hU.isCompact hU.nonempty v).trans
    (mul_le_mul_of_nonneg_right (hausdorffDist_rightErosion_le_of_one_le_width hU hW hε0 hεW)
      (add_nonneg (abs_nonneg _) (abs_nonneg _)))

theorem abs_support_leftErosion_sub_le {U : Set Plane} (hU : IsDownwardCap U)
    (hW : 1 ≤ capWidth U) {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U)
    (v : Plane) :
    |support (leftErosion U ε) v - support U v| ≤ ε * (|v.1| + |v.2|) := by
  have hE := hU.leftErosion hε0 hεW
  exact (abs_support_sub_le_hausdorff hE.isCompact hE.nonempty hU.isCompact hU.nonempty v).trans
    (mul_le_mul_of_nonneg_right (hausdorffDist_leftErosion_le_of_one_le_width hU hW hε0 hεW)
      (add_nonneg (abs_nonneg _) (abs_nonneg _)))

end AmbidextrousSofa
