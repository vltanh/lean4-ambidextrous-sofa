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
    p.1 ∈ Icc (horizontalLeft U) (horizontalRight U) :=
  horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex ▸ ⟨p, hp, rfl⟩

theorem IsDownwardCap.baseline_mem_of_mem_projection {U : Set Plane}
    (hU : IsDownwardCap U) {x : ℝ} (hx : x ∈ horizontalProjection U) :
    (x, 0) ∈ U :=
  hU.baseline_mem (capRoof_mem hU.isCompact hx)

theorem IsDownwardCap.baseline_mem_of_mem_Icc {U : Set Plane} (hU : IsDownwardCap U) {x : ℝ}
    (hx : x ∈ Icc (horizontalLeft U) (horizontalRight U)) : (x, 0) ∈ U :=
  hU.baseline_mem_of_mem_projection
    ((horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex).symm ▸ hx)

theorem IsDownwardCap.inter {U V : Set Plane} (hU : IsDownwardCap U)
    (hV : IsDownwardCap V) (hne : (U ∩ V).Nonempty) :
    IsDownwardCap (U ∩ V) :=
  ⟨hne, hU.isCompact.inter_right hV.isCompact.isClosed, hU.convex.inter hV.convex,
    fun _ hp => hU.inStrip hp.1,
    fun p hp y hy0 hyp => ⟨hU.downward p hp.1 y hy0 hyp, hV.downward p hp.2 y hy0 hyp⟩⟩

/-- Retain a closed interval of actual vertical sections. -/
def horizontalCut (U : Set Plane) (a b : ℝ) : Set Plane :=
  {p | p ∈ U ∧ p.1 ∈ Icc a b}

theorem horizontalCut_subset (U : Set Plane) (a b : ℝ) :
    horizontalCut U a b ⊆ U := fun _ hp => hp.1

theorem IsDownwardCap.horizontalCut {U : Set Plane} (hU : IsDownwardCap U)
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ horizontalProjection U) :
    IsDownwardCap (AmbidextrousSofa.horizontalCut U a b) :=
  ⟨⟨(a, 0), hU.baseline_mem_of_mem_projection (hsub ⟨le_rfl, hab⟩), le_rfl, hab⟩,
    hU.isCompact.inter_right (isClosed_Icc.preimage continuous_fst),
    hU.convex.inter ((convex_Icc a b).linear_preimage (LinearMap.fst ℝ ℝ ℝ)),
    fun _ hp => hU.inStrip hp.1, fun p hp y hy0 hyp => ⟨hU.downward p hp.1 y hy0 hyp, hp.2⟩⟩

theorem horizontalProjection_horizontalCut {U : Set Plane} (hU : IsDownwardCap U)
    {a b : ℝ} (hsub : Icc a b ⊆ horizontalProjection U) :
    horizontalProjection (horizontalCut U a b) = Icc a b :=
  Subset.antisymm (by rintro _ ⟨p, hp, rfl⟩; exact hp.2)
    fun x hx => ⟨(x, 0), ⟨hU.baseline_mem_of_mem_projection (hsub hx), hx⟩, rfl⟩

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
  exact le_antisymm (le_capRoof hU.isCompact (capRoof_mem hC.isCompact
      ((horizontalProjection_horizontalCut hU hsub).symm ▸ hx)).1)
    (le_capRoof hC.isCompact ⟨capRoof_mem hU.isCompact (hsub hx), hx⟩)

/-- An inward right cut uses the original actual projection endpoint. -/
def rightTrim (U : Set Plane) (ε : ℝ) : Set Plane :=
  horizontalCut U (horizontalLeft U) (horizontalRight U - ε)

def leftTrim (U : Set Plane) (ε : ℝ) : Set Plane :=
  horizontalCut U (horizontalLeft U + ε) (horizontalRight U)

theorem rightTrim_subset (U : Set Plane) (ε : ℝ) : rightTrim U ε ⊆ U :=
  horizontalCut_subset U _ _

theorem leftTrim_subset (U : Set Plane) (ε : ℝ) : leftTrim U ε ⊆ U :=
  horizontalCut_subset U _ _

theorem rightTrim_interval_subset {U : Set Plane} (hU : IsDownwardCap U)
    {ε : ℝ} (hε : 0 ≤ ε) :
    Icc (horizontalLeft U) (horizontalRight U - ε) ⊆ horizontalProjection U := by
  rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
  exact Icc_subset_Icc le_rfl (sub_le_self _ hε)

theorem leftTrim_interval_subset {U : Set Plane} (hU : IsDownwardCap U)
    {ε : ℝ} (hε : 0 ≤ ε) :
    Icc (horizontalLeft U + ε) (horizontalRight U) ⊆ horizontalProjection U := by
  rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
  exact Icc_subset_Icc (le_add_of_nonneg_right hε) le_rfl

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

theorem rightErosion_subset (U : Set Plane) (ε : ℝ) : rightErosion U ε ⊆ U :=
  fun _ hp => hp.1

theorem leftErosion_subset (U : Set Plane) (ε : ℝ) : leftErosion U ε ⊆ U :=
  fun _ hp => hp.1

theorem rightErosion_subset_rightTrim {U : Set Plane} (hU : IsDownwardCap U) (ε : ℝ) :
    rightErosion U ε ⊆ rightTrim U ε := fun _ ⟨hp, hq⟩ =>
  ⟨hp, (hU.fst_mem_Icc hp).1, le_sub_iff_add_le.mpr (hU.fst_mem_Icc hq).2⟩

theorem leftErosion_subset_leftTrim {U : Set Plane} (hU : IsDownwardCap U) (ε : ℝ) :
    leftErosion U ε ⊆ leftTrim U ε := fun _ ⟨hp, hq⟩ =>
  ⟨hp, le_sub_iff_add_le.mp (hU.fst_mem_Icc hq).1, (hU.fst_mem_Icc hp).2⟩

theorem IsDownwardCap.rightErosion {U : Set Plane} (hU : IsDownwardCap U)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) :
    IsDownwardCap (AmbidextrousSofa.rightErosion U ε) := by
  unfold capWidth at hεW
  convert hU.inter (hU.horizontalTranslate (-ε)) ⟨(horizontalLeft U, 0),
    hU.baseline_mem_of_mem_Icc ⟨le_rfl, by linarith⟩, (mem_horizontalTranslate_iff _ _ _).mpr
      (hU.baseline_mem_of_mem_Icc (x := horizontalLeft U - -ε) ⟨by linarith, by linarith⟩)⟩
  ext p
  simp [AmbidextrousSofa.rightErosion, mem_horizontalTranslate_iff]

theorem IsDownwardCap.leftErosion {U : Set Plane} (hU : IsDownwardCap U)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U) :
    IsDownwardCap (AmbidextrousSofa.leftErosion U ε) := by
  unfold capWidth at hεW
  convert hU.inter (hU.horizontalTranslate ε) ⟨(horizontalRight U, 0),
    hU.baseline_mem_of_mem_Icc ⟨by linarith, le_rfl⟩, (mem_horizontalTranslate_iff _ _ _).mpr
      (hU.baseline_mem_of_mem_Icc (x := horizontalRight U - ε) ⟨by linarith, by linarith⟩)⟩
  ext p
  simp [AmbidextrousSofa.leftErosion, mem_horizontalTranslate_iff]

theorem horizontalProjection_rightErosion {U : Set Plane} (hU : IsDownwardCap U)
    {ε : ℝ} (hε0 : 0 ≤ ε) :
    horizontalProjection (rightErosion U ε) =
      Icc (horizontalLeft U) (horizontalRight U - ε) :=
  Subset.antisymm (by rintro _ ⟨p, hp, rfl⟩; exact (rightErosion_subset_rightTrim hU ε hp).2)
    fun x hx => ⟨(x, 0), ⟨hU.baseline_mem_of_mem_Icc ⟨hx.1, by linarith [hx.2]⟩,
      hU.baseline_mem_of_mem_Icc (x := x + ε) ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩, rfl⟩

theorem horizontalProjection_leftErosion {U : Set Plane} (hU : IsDownwardCap U)
    {ε : ℝ} (hε0 : 0 ≤ ε) :
    horizontalProjection (leftErosion U ε) =
      Icc (horizontalLeft U + ε) (horizontalRight U) :=
  Subset.antisymm (by rintro _ ⟨p, hp, rfl⟩; exact (leftErosion_subset_leftTrim hU ε hp).2)
    fun x hx => ⟨(x, 0), ⟨hU.baseline_mem_of_mem_Icc ⟨by linarith [hx.1], hx.2⟩,
      hU.baseline_mem_of_mem_Icc (x := x - ε) ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩, rfl⟩

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
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  change max |p.1 - ((1 - lam) * p.1 + lam * a)|
    |p.2 - ((1 - lam) * p.2 + lam * 0)| ≤ lam * max (capWidth U) 1
  rw [show p.1 - ((1 - lam) * p.1 + lam * a) = lam * (p.1 - a) by ring,
    show p.2 - ((1 - lam) * p.2 + lam * 0) = lam * p.2 by ring, abs_mul, abs_mul,
    abs_of_nonneg hlam, ← mul_max_of_nonneg _ _ hlam, capWidth]
  exact mul_le_mul_of_nonneg_left (max_le_max (abs_le.mpr ⟨by linarith [hpx.1, ha.2],
    by linarith [hpx.2, ha.1]⟩) (abs_le.mpr ⟨by linarith [hpy.1], hpy.2⟩)) hlam

theorem exists_erosion_points_dist_le {U : Set Plane} (hU : IsDownwardCap U)
    (hW : 0 < capWidth U) {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U)
    {p : Plane} (hp : p ∈ U) :
    (∃ q ∈ rightErosion U ε, dist p q ≤ (ε / capWidth U) * max (capWidth U) 1) ∧
      ∃ q ∈ leftErosion U ε, dist p q ≤ (ε / capWidth U) * max (capWidth U) 1 := by
  have hlam0 : 0 ≤ ε / capWidth U := div_nonneg hε0 hW.le
  have hlam1 : 0 ≤ 1 - ε / capWidth U := sub_nonneg.mpr ((div_le_one hW).mpr hεW)
  have hlamW : ε / capWidth U * (horizontalRight U - horizontalLeft U) = ε :=
    div_mul_cancel₀ ε hW.ne'
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hL := hU.convex hp (hU.baseline_mem_of_mem_Icc ⟨le_rfl, hlr⟩) hlam1 hlam0 (by ring)
  have hR := hU.convex hp (hU.baseline_mem_of_mem_Icc ⟨hlr, le_rfl⟩) hlam1 hlam0 (by ring)
  refine ⟨⟨_, ⟨hL, ?_⟩, dist_baseline_contraction_le hU hp ⟨le_rfl, hlr⟩ hlam0⟩,
    ⟨_, ⟨hR, ?_⟩, dist_baseline_contraction_le hU hp ⟨hlr, le_rfl⟩ hlam0⟩⟩ <;>
    [convert hR using 1; convert hL using 1] <;> refine Prod.ext ?_ rfl <;>
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] <;> linarith

theorem abs_support_sub_le_of_close {U V : Set Plane} (hU : IsDownwardCap U)
    (hV : IsDownwardCap V) (hVU : V ⊆ U) (hW : 1 ≤ capWidth U) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hclose : ∀ p ∈ U, ∃ q ∈ V, dist p q ≤ (ε / capWidth U) * max (capWidth U) 1)
    (v : Plane) : |support V v - support U v| ≤ ε * (|v.1| + |v.2|) := by
  rw [max_eq_left hW, div_mul_cancel₀ ε (zero_lt_one.trans_le hW).ne'] at hclose
  exact (abs_support_sub_le_hausdorff hV.isCompact hV.nonempty hU.isCompact hU.nonempty v).trans
    (mul_le_mul_of_nonneg_right (Metric.hausdorffDist_le_of_mem_dist hε0
      (fun p hp => ⟨p, hVU hp, by simpa using hε0⟩) hclose) (by positivity))

theorem abs_support_rightTrim_sub_le {U : Set Plane} (hU : IsDownwardCap U)
    (hW : 1 ≤ capWidth U) {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U)
    (v : Plane) :
    |support (rightTrim U ε) v - support U v| ≤ ε * (|v.1| + |v.2|) :=
  abs_support_sub_le_of_close hU (hU.rightTrim hε0 hεW) (rightTrim_subset U ε) hW hε0
    (fun _ hp => (exists_erosion_points_dist_le hU (zero_lt_one.trans_le hW) hε0 hεW
      hp).1.imp fun _ ⟨hq, hd⟩ => ⟨rightErosion_subset_rightTrim hU ε hq, hd⟩) v

theorem abs_support_leftTrim_sub_le {U : Set Plane} (hU : IsDownwardCap U)
    (hW : 1 ≤ capWidth U) {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U)
    (v : Plane) :
    |support (leftTrim U ε) v - support U v| ≤ ε * (|v.1| + |v.2|) :=
  abs_support_sub_le_of_close hU (hU.leftTrim hε0 hεW) (leftTrim_subset U ε) hW hε0
    (fun _ hp => (exists_erosion_points_dist_le hU (zero_lt_one.trans_le hW) hε0 hεW
      hp).2.imp fun _ ⟨hq, hd⟩ => ⟨leftErosion_subset_leftTrim hU ε hq, hd⟩) v

theorem abs_support_rightErosion_sub_le {U : Set Plane} (hU : IsDownwardCap U)
    (hW : 1 ≤ capWidth U) {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U)
    (v : Plane) :
    |support (rightErosion U ε) v - support U v| ≤ ε * (|v.1| + |v.2|) :=
  abs_support_sub_le_of_close hU (hU.rightErosion hε0 hεW) (rightErosion_subset U ε) hW hε0
    (fun _ hp => (exists_erosion_points_dist_le hU (zero_lt_one.trans_le hW) hε0 hεW hp).1) v

theorem abs_support_leftErosion_sub_le {U : Set Plane} (hU : IsDownwardCap U)
    (hW : 1 ≤ capWidth U) {ε : ℝ} (hε0 : 0 ≤ ε) (hεW : ε ≤ capWidth U)
    (v : Plane) :
    |support (leftErosion U ε) v - support U v| ≤ ε * (|v.1| + |v.2|) :=
  abs_support_sub_le_of_close hU (hU.leftErosion hε0 hεW) (leftErosion_subset U ε) hW hε0
    (fun _ hp => (exists_erosion_points_dist_le hU (zero_lt_one.trans_le hW) hε0 hεW hp).2) v

end AmbidextrousSofa
