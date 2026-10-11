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

/-- A literal top point and the right baseline point make the full
niche strictly positive between their two relevant abscissae. -/
theorem IsDownwardCap.sweptNiche_pos_of_top_point_left
    {U : Set Plane} (hU : IsDownwardCap U) {a x : ℝ}
    (htop : (a, 1) ∈ U) (hax : a < x) (hxr : x < horizontalRight U - 1) :
    0 < sweptNiche U (Real.pi / 2) x := by
  obtain ⟨k, hk, hkbound⟩ := exists_between (lt_min (zero_lt_one' ℝ)
    (lt_min (sub_pos.mpr hax) (by linarith : 0 < horizontalRight U - 1 - x)))
  simp only [lt_min_iff] at hkbound
  have hb : nearDiagonalNorm k ≤ 1 + k ^ 2 / 2 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by linarith [sq_nonneg (k ^ 2)]⟩
  have hR := coordDot_le_support hU.isCompact hU.right_baseline_mem (1, k)
  have hL := coordDot_le_support hU.isCompact htop (-k, 1)
  simp only [coordDot] at hR hL
  refine (lt_min ?_ ?_ : 0 < cornerWall U (Real.arctan k) x).trans_le (cornerWall_le_sweptNiche
    (sweptWallValues_bddAbove hU.isCompact le_rfl x)
    ⟨Real.arctan_pos.mpr hk, Real.arctan_lt_pi_div_two k⟩)
  · rw [hU.firstWall_arctan hk.ne']
    exact div_pos (by linarith [mul_pos hk (sub_pos.mpr hkbound.1)]) hk
  · rw [hU.secondWall_arctan]
    linarith [mul_pos hk (sub_pos.mpr hkbound.2.1), sq_nonneg k]

theorem IsDownwardCap.sweptNiche_pos_of_top_point_right
    {U : Set Plane} (hU : IsDownwardCap U) {b x : ℝ}
    (htop : (b, 1) ∈ U) (hxb : x < b) (hlx : horizontalLeft U + 1 < x) :
    0 < sweptNiche U (Real.pi / 2) x := by
  have h := hU.horizontalMirror.sweptNiche_pos_of_top_point_left
    ((mem_horizontalMirror_iff U (-b, 1)).mpr (by simpa [horizontalReflection] using htop))
    (neg_lt_neg hxb) (by rw [horizontalRight_horizontalMirror hU]; linarith)
  simpa only [sweptNiche_horizontalMirror, neg_neg] using h

/-- Width greater than two makes the two positive intervals overlap.
Only actual middle endpoint heights are needed, with no curvature law. -/
theorem IsDownwardCap.sweptNiche_pos_on_open_middle_of_unit_endpoints
    {U : Set Plane} (hU : IsDownwardCap U) (hwidth : 2 < capWidth U)
    (hleft : capRoof U (horizontalLeft U + capWidth U / 4) = 1)
    (hright : capRoof U (horizontalRight U - capWidth U / 4) = 1) :
    ∀ x ∈ Ioo (horizontalLeft U + capWidth U / 4)
      (horizontalRight U - capWidth U / 4), 0 < sweptNiche U (Real.pi / 2) x := by
  have hmem {y : ℝ} (hy : capRoof U y = 1) (h1 : horizontalLeft U ≤ y)
      (h2 : y ≤ horizontalRight U) : (y, 1) ∈ U :=
    hy ▸ capRoof_mem hU.isCompact
      (hU.horizontalProjection_eq_Icc ▸ ⟨h1, h2⟩)
  unfold capWidth at *
  intro x hx
  rcases lt_or_ge x (horizontalRight U - 1) with hxr | hxr
  · exact hU.sweptNiche_pos_of_top_point_left (hmem hleft (by linarith) (by linarith)) hx.1 hxr
  · exact hU.sweptNiche_pos_of_top_point_right (hmem hright (by linarith) (by linarith)) hx.2
      (by linarith)

end AmbidextrousSofa
