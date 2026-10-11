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

theorem IsDownwardCap.middle_face_projection_eq_empty {U : Set Plane}
    (hU : IsDownwardCap U) {t : ℝ} (hs : 0 ≤ Real.sin t)
    (hsep : Real.sin t < capWidth U / 4 * |Real.cos t|) :
    Ioc (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) ∩
        horizontalProjection (MovingSofaOptimality.edge U t) = ∅ := by
  refine eq_empty_of_forall_notMem ?_
  rintro _ ⟨hx, p, hp, rfl⟩
  have hface : coordDot p (unitNormal t) = support U (unitNormal t) := hp.2
  have hbase (q : ℝ) (hq : q ∈ horizontalProjection U) :
      q * Real.cos t ≤ p.1 * Real.cos t + p.2 * Real.sin t := by
    have := coordDot_le_support hU.isCompact (hU.baseline_mem (capRoof_mem hU.isCompact hq))
      (unitNormal t)
    rw [← hface] at this
    simpa only [coordDot, unitNormal, zero_mul, add_zero] using this
  have hR := hbase _ (horizontalRight_mem hU.nonempty hU.isCompact)
  have hL := hbase _ (horizontalLeft_mem hU.nonempty hU.isCompact)
  have hy := mul_le_mul_of_nonneg_right (hU.inStrip hp.1).2 hs
  unfold capWidth at hsep
  rcases le_or_gt 0 (Real.cos t) with hc | hc
  · rw [abs_of_nonneg hc] at hsep
    linarith [mul_le_mul_of_nonneg_right hx.2 hc]
  · rw [abs_of_neg hc] at hsep
    linarith [mul_le_mul_of_nonneg_right hx.1.le (neg_nonneg.mpr hc.le)]

namespace AngularGrid

open FinitePolygon

def axisCutoff (w : ℝ) : ℝ := min (Real.pi / 4) (w / 16)

theorem axisCutoff_pos {w : ℝ} (hw : 0 < w) : 0 < axisCutoff w :=
  lt_min (by positivity) (by positivity)

theorem small_angle_separation {w W t : ℝ} (hw : 0 < w) (hW : w ≤ W)
    (ht : t ∈ Ioc (0 : ℝ) (axisCutoff w)) :
    Real.sin t < W / 4 * |Real.cos t| := by
  obtain ⟨ht0, ht⟩ := ht
  have hπ : t ≤ Real.pi / 4 := ht.trans (min_le_left _ _)
  have hc : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rw [abs_of_pos hc, ← div_lt_iff₀ hc, ← Real.tan_eq_sin_div_cos]
  calc Real.tan t ≤ 2 * t := tan_le_two_mul ⟨ht0.le, hπ⟩
    _ ≤ w / 8 := by linarith [ht.trans (min_le_right _ _)]
    _ < W / 4 := by linarith

/-- The same cutoff works at both horizontal axes. -/
theorem middleOuterMass_eq_zero_near_axes {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (hpoly : U = circumscription U (normal grid))
    {w : ℝ} (hw : 0 < w) (hW : w ≤ capWidth U) (j : SourceIndex grid)
    (ht : fullAngle grid j ≤ axisCutoff w ∨ Real.pi - fullAngle grid j ≤ axisCutoff w) :
    middleOuterMass U grid j = 0 := by
  classical
  have hangle := fullAngle_mem grid j
  have hsep : Real.sin (fullAngle grid j) < capWidth U / 4 * |Real.cos (fullAngle grid j)| := by
    rcases ht with ht | ht
    · exact small_angle_separation hw hW ⟨hangle.1, ht⟩
    · simpa only [Real.sin_pi_sub, Real.cos_pi_sub, abs_neg] using
        small_angle_separation (t := Real.pi - fullAngle grid j) hw hW ⟨by linarith [hangle.2], ht⟩
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  refine (integral_outerSource_eq_clipped_projection hU (normal grid) (normal_snd_pos grid)
    (wallSlopes_injective grid) hpoly j (normal_eq_unitNormal grid j) (by linarith)
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩).trans ?_
  rw [hU.middle_face_projection_eq_empty
    (Real.sin_nonneg_of_nonneg_of_le_pi hangle.1.le hangle.2.le) hsep, measureReal_empty, zero_div]

theorem IsSelectedPolygon.curvature_atom_coarse_near_axes {target U : Set Plane}
    {a b coefficient R w : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hcoefficient : 0 ≤ coefficient)
    (hR : 0 ≤ R) (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hw : 0 < w) (hW : w ≤ capWidth U) (j : SourceIndex (dyadic level))
    (ht : fullAngle (dyadic level) j ≤ axisCutoff w ∨
      Real.pi - fullAngle (dyadic level) j ≤ axisCutoff w) :
    (upperCurvature U {fullAngle (dyadic level) j}).toReal ≤
      (4 * R + 10) * mesh level + selectionDefect target U level coefficient j := by
  simpa only [middleOuterMass_eq_zero_near_axes hU.isCap _ hU.polygon_eq hw hW j ht, add_zero]
    using hU.curvature_atom_coarse hcoefficient hR hbox j

end AngularGrid

end AmbidextrousSofa
