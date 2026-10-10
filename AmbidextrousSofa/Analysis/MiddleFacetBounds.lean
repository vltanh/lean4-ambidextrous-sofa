module

public import AmbidextrousSofa.Analysis.BoxedSecants

@[expose] public section

/-!
# Middle facets stay uniformly away from the horizontal axes

An upper supporting face through the middle window must lie above both
baseline endpoints. Since the cap height is at most one, this imposes an
explicit lower bound on the normal's vertical component. It eliminates
the retained middle-facet term on uniform angular neighborhoods of the
axes whenever the width has a positive lower bound.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem IsDownwardCap.middle_face_width_bound {U : Set Plane} (hU : IsDownwardCap U)
    {t : ℝ} (hs : 0 ≤ Real.sin t) {p : Plane} (hp : p ∈ MovingSofaOptimality.edge U t)
    (hx : p.1 ∈ Icc
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4)) :
    capWidth U / 4 * |Real.cos t| ≤ Real.sin t := by
  have hface : coordDot p (unitNormal t) = support U (unitNormal t) := hp.2
  have hy := mul_le_mul_of_nonneg_right (hU.inStrip hp.1).2 hs
  by_cases hc : 0 ≤ Real.cos t
  · have hr : (horizontalRight U, 0) ∈ U :=
      hU.baseline_mem (capRoof_mem hU.isCompact (horizontalRight_mem hU.nonempty hU.isCompact))
    have hdot := coordDot_le_support hU.isCompact hr (unitNormal t)
    rw [← hface] at hdot
    simp only [coordDot, unitNormal, zero_mul, add_zero] at hdot
    have hdist : capWidth U / 4 ≤ horizontalRight U - p.1 := by
      unfold capWidth
      linarith [hx.2]
    have hmul := mul_le_mul_of_nonneg_right hdist hc
    rw [abs_of_nonneg hc]
    nlinarith
  · have hl : (horizontalLeft U, 0) ∈ U :=
      hU.baseline_mem (capRoof_mem hU.isCompact (horizontalLeft_mem hU.nonempty hU.isCompact))
    have hdot := coordDot_le_support hU.isCompact hl (unitNormal t)
    rw [← hface] at hdot
    simp only [coordDot, unitNormal, zero_mul, add_zero] at hdot
    have hdist : capWidth U / 4 ≤ p.1 - horizontalLeft U := by
      unfold capWidth
      linarith [hx.1]
    have hmul := mul_le_mul_of_nonneg_right hdist (neg_nonneg.mpr (le_of_not_ge hc))
    rw [abs_of_nonpos (le_of_not_ge hc)]
    nlinarith

theorem IsDownwardCap.middle_face_projection_eq_empty {U : Set Plane}
    (hU : IsDownwardCap U) {t : ℝ} (hs : 0 ≤ Real.sin t)
    (hsep : Real.sin t < capWidth U / 4 * |Real.cos t|) :
    Ioc (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) ∩
        horizontalProjection (MovingSofaOptimality.edge U t) = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  rintro x ⟨hx, p, hp, hpx⟩
  have hx' : p.1 ∈ Icc
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) := by
    rw [hpx]
    exact ⟨hx.1.le, hx.2⟩
  exact (hU.middle_face_width_bound hs hp hx').not_gt hsep

namespace AngularGrid

open FinitePolygon

theorem middleOuterMass_eq_zero_of_axis_separation {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (hpoly : U = circumscription U (normal grid))
    (j : SourceIndex grid)
    (hsep : Real.sin (fullAngle grid j) < capWidth U / 4 * |Real.cos (fullAngle grid j)|) :
    middleOuterMass U grid j = 0 := by
  classical
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hwindow : Ioc
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) ⊆
        Icc (horizontalLeft U) (horizontalRight U) := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hsin : 0 < Real.sin (fullAngle grid j) := by
    simpa only [normal_eq_unitNormal, unitNormal] using normal_snd_pos grid j
  have h := integral_outerSource_eq_clipped_projection hU (normal grid)
    (normal_snd_pos grid) (wallSlopes_injective grid) hpoly j (normal_eq_unitNormal grid j)
    (by linarith : horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 ≤
      horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) hwindow
  change middleOuterMass U grid j =
    volume.real (Ioc
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) ∩
        horizontalProjection (MovingSofaOptimality.edge U (fullAngle grid j))) /
          Real.sin (fullAngle grid j) at h
  rw [hU.middle_face_projection_eq_empty hsin.le hsep] at h
  simpa only [measureReal_empty, zero_div] using h

def axisCutoff (w : ℝ) : ℝ := min (Real.pi / 4) (w / 16)

theorem axisCutoff_pos {w : ℝ} (hw : 0 < w) : 0 < axisCutoff w := by
  unfold axisCutoff
  exact lt_min (by linarith [Real.pi_pos]) (by linarith)

theorem small_angle_separation {w W t : ℝ} (hw : 0 < w) (hW : w ≤ W)
    (ht : t ∈ Ioc (0 : ℝ) (axisCutoff w)) :
    Real.sin t < W / 4 * |Real.cos t| := by
  have htquarter : t ≤ Real.pi / 4 := ht.2.trans (min_le_left _ _)
  have htw : t ≤ w / 16 := ht.2.trans (min_le_right _ _)
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [ht.1, Real.pi_pos], by linarith [htquarter, Real.pi_pos]⟩
  have htan := tan_le_two_mul ⟨ht.1.le, htquarter⟩
  have hstrict : Real.tan t < W / 4 := by linarith
  rw [Real.tan_eq_sin_div_cos, div_lt_iff₀ hc] at hstrict
  simpa only [abs_of_nonneg hc.le] using hstrict

/-- The same cutoff works at both horizontal axes. -/
theorem middleOuterMass_eq_zero_near_axes {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (hpoly : U = circumscription U (normal grid))
    {w : ℝ} (hw : 0 < w) (hW : w ≤ capWidth U) (j : SourceIndex grid)
    (ht : fullAngle grid j ≤ axisCutoff w ∨ Real.pi - fullAngle grid j ≤ axisCutoff w) :
    middleOuterMass U grid j = 0 := by
  apply middleOuterMass_eq_zero_of_axis_separation hU grid hpoly j
  have hangle := fullAngle_mem grid j
  rcases ht with ht | ht
  · exact small_angle_separation hw hW ⟨hangle.1, ht⟩
  · have h := small_angle_separation hw hW
      (show Real.pi - fullAngle grid j ∈ Ioc (0 : ℝ) (axisCutoff w) from
        ⟨by linarith [hangle.2], ht⟩)
    simpa only [Real.sin_pi_sub, Real.cos_pi_sub, abs_neg] using h

theorem IsSelectedPolygon.curvature_atom_coarse_near_axes {target U : Set Plane}
    {a b coefficient R w : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hcoefficient : 0 ≤ coefficient)
    (hR : 0 ≤ R) (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hw : 0 < w) (hW : w ≤ capWidth U) (j : SourceIndex (dyadic level))
    (ht : fullAngle (dyadic level) j ≤ axisCutoff w ∨
      Real.pi - fullAngle (dyadic level) j ≤ axisCutoff w) :
    (upperCurvature U {fullAngle (dyadic level) j}).toReal ≤
      (4 * R + 10) * mesh level + selectionDefect target U level coefficient j := by
  have h := hU.curvature_atom_coarse hcoefficient hR hbox j
  rw [middleOuterMass_eq_zero_near_axes hU.isCap _ hU.polygon_eq hw hW j ht, add_zero] at h
  exact h

end AngularGrid

end AmbidextrousSofa
