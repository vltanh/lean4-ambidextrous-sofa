module

public import AmbidextrousSofa.Analysis.NearDiagonalWalls
public import AmbidextrousSofa.Analysis.CapReflection

@[expose] public section

/-!
# Actual positive niche from a top point and a baseline endpoint

Two points of the original cap already supply strictly positive attached
walls at a sufficiently small angle. This avoids a support-derivative
asymptotic at the axis. Reflection and width greater than two cover the
entire open middle interval when both middle endpoints have height one.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem nearDiagonalNorm_le_one_add_half_sq (k : ℝ) :
    nearDiagonalNorm k ≤ 1 + k ^ 2 / 2 := by
  have hb := nearDiagonalNorm_pos k
  have hbsq := nearDiagonalNorm_sq k
  by_contra h
  have hprod := mul_pos
    (sub_pos.mpr (lt_of_not_ge h))
    (show 0 < nearDiagonalNorm k + (1 + k ^ 2 / 2) by positivity)
  nlinarith only [hbsq, hprod, sq_nonneg (k ^ 2)]

/-- A literal top point and the right baseline point make the full
niche strictly positive between their two relevant abscissae. -/
theorem IsDownwardCap.sweptNiche_pos_of_top_point_left
    {U : Set Plane} (hU : IsDownwardCap U) {a x : ℝ}
    (htop : (a, 1) ∈ U) (hax : a < x) (hxr : x < horizontalRight U - 1) :
    0 < sweptNiche U (Real.pi / 2) x := by
  have hgap : 0 < horizontalRight U - 1 - x := by linarith only [hxr]
  obtain ⟨k, hk, hkbound⟩ := exists_between
    (lt_min (by norm_num : (0 : ℝ) < 1) (lt_min (sub_pos.mpr hax) hgap))
  have hk1 : k < 1 := (lt_min_iff.mp hkbound).1
  have hkd : k < x - a := (lt_min_iff.mp (lt_min_iff.mp hkbound).2).1
  have hkgap : k < horizontalRight U - 1 - x :=
    (lt_min_iff.mp (lt_min_iff.mp hkbound).2).2
  have hb := nearDiagonalNorm_le_one_add_half_sq k
  have hsqk : k ^ 2 < k := by
    nlinarith only [mul_pos hk (sub_pos.mpr hk1)]
  have hright : nearDiagonalNorm k < horizontalRight U - x := by
    linarith only [hb, hsqk, hkgap, hk]
  have hleft : nearDiagonalNorm k < 1 + k * (x - a) := by
    have hprod := mul_pos hk (sub_pos.mpr hkd)
    nlinarith only [hb, hprod, sq_nonneg k]
  have hRsupport : horizontalRight U ≤ support U (1, k) := by
    simpa only [coordDot, mul_one, zero_mul, add_zero] using
      coordDot_le_support hU.isCompact hU.right_baseline_mem (1, k)
  have hLsupport : 1 - k * a ≤ support U (-k, 1) := by
    have h := coordDot_le_support hU.isCompact htop (-k, 1)
    simp only [coordDot, one_mul, mul_neg] at h
    nlinarith only [h]
  have hR : 0 < firstWall U (Real.arctan k) x := by
    rw [hU.firstWall_arctan hk.ne']
    exact div_pos (by linarith only [hRsupport, hright]) hk
  have hL : 0 < secondWall U (Real.arctan k) x := by
    rw [hU.secondWall_arctan]
    nlinarith only [hLsupport, hleft]
  have hcorner : 0 < cornerWall U (Real.arctan k) x := lt_min hR hL
  exact hcorner.trans_le (cornerWall_le_sweptNiche
    (sweptWallValues_bddAbove hU.isCompact (le_refl (Real.pi / 2)) x)
    ⟨Real.arctan_pos.mpr hk, Real.arctan_lt_pi_div_two k⟩)

theorem IsDownwardCap.sweptNiche_pos_of_top_point_right
    {U : Set Plane} (hU : IsDownwardCap U) {b x : ℝ}
    (htop : (b, 1) ∈ U) (hxb : x < b) (hlx : horizontalLeft U + 1 < x) :
    0 < sweptNiche U (Real.pi / 2) x := by
  have htop' : (-b, 1) ∈ AmbidextrousSofa.horizontalMirror U := by
    rw [mem_horizontalMirror_iff]
    simpa only [horizontalReflection, neg_neg] using htop
  have hbound : -x < horizontalRight (AmbidextrousSofa.horizontalMirror U) - 1 := by
    rw [horizontalRight_horizontalMirror hU]
    linarith only [hlx]
  have h := hU.horizontalMirror.sweptNiche_pos_of_top_point_left htop'
    (by linarith only [hxb] : -b < -x) hbound
  simpa only [sweptNiche_horizontalMirror, neg_neg] using h

/-- Width greater than two makes the two positive intervals overlap.
Only actual middle endpoint heights are needed, with no curvature law. -/
theorem IsDownwardCap.sweptNiche_pos_on_open_middle_of_unit_endpoints
    {U : Set Plane} (hU : IsDownwardCap U) (hwidth : 2 < capWidth U)
    (hleft : capRoof U (horizontalLeft U + capWidth U / 4) = 1)
    (hright : capRoof U (horizontalRight U - capWidth U / 4) = 1) :
    ∀ x ∈ Ioo (horizontalLeft U + capWidth U / 4)
      (horizontalRight U - capWidth U / 4), 0 < sweptNiche U (Real.pi / 2) x := by
  have hwidth0 : 0 < capWidth U := by linarith only [hwidth]
  have hA : horizontalLeft U + capWidth U / 4 ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
    unfold capWidth at hwidth0 ⊢
    constructor <;> linarith only [hwidth0]
  have hB : horizontalRight U - capWidth U / 4 ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
    unfold capWidth at hwidth0 ⊢
    constructor <;> linarith only [hwidth0]
  have hpA : (horizontalLeft U + capWidth U / 4, 1) ∈ U := by
    simpa only [hleft] using capRoof_mem hU.isCompact hA
  have hpB : (horizontalRight U - capWidth U / 4, 1) ∈ U := by
    simpa only [hright] using capRoof_mem hU.isCompact hB
  intro x hx
  by_cases hxr : x < horizontalRight U - 1
  · exact hU.sweptNiche_pos_of_top_point_left hpA hx.1 hxr
  · apply hU.sweptNiche_pos_of_top_point_right hpB hx.2
    unfold capWidth at hwidth
    linarith only [hwidth, le_of_not_gt hxr]

end AmbidextrousSofa
