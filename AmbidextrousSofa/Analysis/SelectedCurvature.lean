module

public import AmbidextrousSofa.Analysis.FacetCurvature

@[expose] public section

/-!
# Actual selected curvature atoms with the uncharged middle face retained

Only the exterior roof is charged by the spatial score. Consequently its
finite variation controls the entire curvature atom after adding back the
actual middle part of that outer facet. This term is retained explicitly;
it is not erased by an angular objective or an assumed regularity field.
The support-penalty errors have a proved summable bound tending to zero
along the actual selected sequence.

Both estimates are proved for an arbitrary grid, inner barrier and penalty
weights, so that they also serve the proper-angle polygons.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace FinitePolygon

variable {ι : Type*}

theorem outward_sourceDensity_nonneg [DecidableEq ι] (e : WallExpr (Option ι))
    (normal : ι → Plane) (intercept : Option ι → ℝ) (j : ι)
    (hny : 0 ≤ (normal j).2) (x : ℝ) :
    0 ≤ e.sourceDensity (wallSlope normal) intercept (outwardVelocity normal j) x := by
  rw [outwardVelocity_eq_single, e.sourceDensity_single]
  exact Set.indicator_nonneg (fun _ _ => div_nonneg (by norm_num) hny) x

theorem intervalIntegrable_outward_sourceDensity [DecidableEq ι]
    (e : WallExpr (Option ι)) (normal : ι → Plane) (intercept : Option ι → ℝ)
    (j : ι) (a b : ℝ) :
    IntervalIntegrable (e.sourceDensity (wallSlope normal) intercept (outwardVelocity normal j))
      volume a b := by
  rw [outwardVelocity_eq_single, e.sourceDensity_single]
  exact (continuous_const.integrableOn_uIcc.indicator
    (e.measurableSet_sourceSet _ _ _)).intervalIntegrable

end FinitePolygon

namespace AngularGrid

open FinitePolygon

def outerDensity (U : Set Plane) (grid : Finset QuarterAngle) (j : SourceIndex grid) : ℝ → ℝ := by
  classical
  exact (roofExpr (ι := SourceIndex grid)).sourceDensity (wallSlope (normal grid))
    (roofIntercept (normal grid) (fun i => support U (normal grid i)))
    (outwardVelocity (normal grid) j)

def innerDensity (U : Set Plane) (grid : Finset QuarterAngle) (j : SourceIndex grid) : ℝ → ℝ := by
  classical
  exact (barrierExpr (pairList grid) none).sourceDensity (wallSlope (normal grid))
    (barrierIntercept (normal grid) (fun i => support U (normal grid i)))
    (outwardVelocity (normal grid) j)

theorem outerDensity_nonneg (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex grid) (x : ℝ) : 0 ≤ outerDensity U grid j x :=
  outward_sourceDensity_nonneg _ _ _ _ (normal_snd_pos grid j).le x

theorem innerDensity_nonneg (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex grid) (x : ℝ) : 0 ≤ innerDensity U grid j x :=
  outward_sourceDensity_nonneg _ _ _ _ (normal_snd_pos grid j).le x

theorem intervalIntegrable_outerDensity (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex grid) (a b : ℝ) : IntervalIntegrable (outerDensity U grid j) volume a b :=
  intervalIntegrable_outward_sourceDensity _ _ _ _ a b

theorem intervalIntegrable_innerDensity (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex grid) (a b : ℝ) : IntervalIntegrable (innerDensity U grid j) volume a b :=
  intervalIntegrable_outward_sourceDensity _ _ _ _ a b

def selectionDefect (target U : Set Plane) (level : ℕ) (coefficient : ℝ)
    (j : SourceIndex (dyadic level)) : ℝ :=
  2 * coefficient * stageWeight level j *
    |support U (normal (dyadic level) j) - support target (normal (dyadic level) j)|

theorem selectionDefect_nonneg (target U : Set Plane) (level : ℕ)
    {coefficient : ℝ} (hcoefficient : 0 ≤ coefficient) (j : SourceIndex (dyadic level)) :
    0 ≤ selectionDefect target U level coefficient j :=
  mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hcoefficient) (stageWeight_nonneg level j))
    (abs_nonneg _)

/-- The source atom estimate for a polygon on any grid that maximizes the spatial score minus
`c * sampledPenalty V (normal grid) w s` among the caps `V` in its box. A zero atom is included
without requiring a positive-face variation. -/
theorem curvature_atom_le_of_maximizes {grid : Finset QuarterAngle} {U : Set Plane}
    {a b c : ℝ} {w s : SourceIndex grid → ℝ}
    (corners : List (SourceIndex grid × SourceIndex grid)) (terminal : Option (SourceIndex grid))
    (hU : IsDownwardCap U) (hbox : U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hpoly : U = circumscription U (normal grid)) (hc : 0 ≤ c) (hw : ∀ i, 0 ≤ w i)
    (hmax : ∀ V : Set Plane, IsDownwardCap V → V ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 →
      finiteSpatialScore V (normal grid) corners terminal -
          c * sampledPenalty V (normal grid) w s ≤
        finiteSpatialScore U (normal grid) corners terminal -
          c * sampledPenalty U (normal grid) w s)
    (j : SourceIndex grid) :
    (upperCurvature U {fullAngle grid j}).toReal ≤
      (∫ x in (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)..
        (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4),
        (barrierExpr corners terminal).sourceDensity (wallSlope (normal grid))
          (barrierIntercept (normal grid) fun i => support U (normal grid i))
          (outwardVelocity (normal grid) j) x) +
      (∫ x in (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)..
        (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4),
        outerDensity U grid j x) + 2 * c * w j * |support U (normal grid j) - s j| := by
  classical
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  rcases ENNReal.toReal_nonneg.eq_or_lt with hmass | hmass
  · rw [← hmass]
    refine add_nonneg (add_nonneg ?_ ?_)
      (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hc) (hw j)) (abs_nonneg _)) <;>
      exact intervalIntegral.integral_nonneg_of_forall (by linarith) fun x =>
        outward_sourceDensity_nonneg _ _ _ j (normal_snd_pos grid j).le x
  have hcb := hU.imported_isConvexBody
  have hp := MovingSofaOptimality.vminus_mem_edge hcb (fullAngle grid j)
  have hq := MovingSofaOptimality.vplus_mem_edge hcb (fullAngle grid j)
  have hpq : MovingSofaOptimality.vminus U (fullAngle grid j) ≠
      MovingSofaOptimality.vplus U (fullAngle grid j) := fun heq => hmass.ne' <| by
    change MovingSofaOptimality.sigmaAt U _ = 0
    rw [(MovingSofaOptimality.proposition2_1_2 hcb _).1, heq, sub_self]
    simp [MovingSofaOptimality.norm2, MovingSofaOptimality.dot]
  have hExpose := selected_polygon_exposure_inequality (normal grid) _ (fun i => c * w i) s
    corners terminal j hlr (normal_snd_pos grid) (wallSlopes_injective grid)
    (circumscription_baseline hU _) (support_circumscription hU _)
    (subset_circumscription hU _ hp.1) (subset_circumscription hU _ hq.1) hpq
    (by rw [normal_eq_unitNormal]; exact hp.2) (by rw [normal_eq_unitNormal]; exact hq.2)
    (normal_fst_ne_zero grid j) (fun i hij => normal_det_ne_zero grid (Ne.symm hij))
    (normal_unit grid j) fun V hV hproj => by
      have hVB : V ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 := fun p hpV => by
        obtain ⟨q, hqU, hqx⟩ : p.1 ∈ horizontalProjection U := by
          rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, ← hproj]
          exact ⟨p, hpV, rfl⟩
        exact ⟨hqx ▸ (hbox hqU).1, hV.inStrip hpV⟩
      rw [show upperPolygon _ _ _ _ = U from hpoly.symm]
      simpa only [sampledPenalty_mul] using hmax V hV hVB
  have htotal := integral_outerSource_eq_curvature_atom hU (normal grid) (normal_snd_pos grid)
    (wallSlopes_injective grid) hpoly j (normal_eq_unitNormal grid j)
  have hfirst := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_outerDensity U grid j (horizontalLeft U)
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4))
    (intervalIntegrable_outerDensity U grid j _
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4))
  have hlast := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_outerDensity U grid j (horizontalLeft U)
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4))
    (intervalIntegrable_outerDensity U grid j _ (horizontalRight U))
  unfold outerDensity at *
  linarith [mul_le_mul_of_nonneg_left (le_abs_self (support U (normal grid j) - s j))
    (mul_nonneg hc (hw j))]

/-- The actual source atom estimate. A zero atom is included without
requiring a positive-face variation. -/
theorem IsSelectedPolygon.curvature_atom_le {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hcoefficient : 0 ≤ coefficient)
    (j : SourceIndex (dyadic level)) :
    (upperCurvature U {fullAngle (dyadic level) j}).toReal ≤
      (∫ x in (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)..
        (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4),
        innerDensity U (dyadic level) j x) +
      (∫ x in (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)..
        (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4),
        outerDensity U (dyadic level) j x) + selectionDefect target U level coefficient j :=
  curvature_atom_le_of_maximizes (pairList (dyadic level)) none hU.isCap hU.inBox hU.polygon_eq
    hcoefficient (stageWeight_nonneg level) hU.maximizes j

/-- Weighted support defects vanish along a Hausdorff convergent sequence when the weights sum
to at most one and the coefficients tend to zero. -/
theorem supportDefect_sum_tendsto {target : Set Plane} {U : ℕ → Set Plane}
    {grid : ℕ → Finset QuarterAngle} {coefficient : ℕ → ℝ} {w : ∀ n, SourceIndex (grid n) → ℝ}
    (hTarget : IsDownwardCap target) (hU : ∀ n, IsDownwardCap (U n))
    (hcoefficient : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hw : ∀ n j, 0 ≤ w n j) (hw1 : ∀ n, ∑ j, w n j ≤ 1)
    (hHausdorff : CapHausdorffTendsto U target) :
    Tendsto (fun n => ∑ j, 2 * coefficient n * w n j *
      |support (U n) (normal (grid n) j) - support target (normal (grid n) j)|) atTop (𝓝 0) := by
  refine squeeze_zero (fun n => Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg
    (mul_nonneg zero_le_two (hcoefficient n)) (hw n j)) (abs_nonneg _)) (fun n => ?_)
    (by simpa only [mul_zero] using (hrate.const_mul 4).mul hHausdorff)
  have hd := Metric.hausdorffDist_nonneg (s := U n) (t := target)
  have hc := hcoefficient n
  calc (∑ j, 2 * coefficient n * w n j *
        |support (U n) (normal (grid n) j) - support target (normal (grid n) j)|)
      ≤ ∑ j, 4 * coefficient n * Metric.hausdorffDist (U n) target * w n j := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hn : |(normal (grid n) j).1| + |(normal (grid n) j).2| ≤ 2 := by
          rw [normal_eq_unitNormal]
          exact (add_le_add (Real.abs_cos_le_one _) (Real.abs_sin_le_one _)).trans_eq
            one_add_one_eq_two
        have h := (abs_support_sub_le_hausdorff (hU n).isCompact (hU n).nonempty
          hTarget.isCompact hTarget.nonempty (normal (grid n) j)).trans
            (mul_le_mul_of_nonneg_left hn hd)
        exact (mul_le_mul_of_nonneg_left h
          (mul_nonneg (mul_nonneg zero_le_two hc) (hw n j))).trans_eq (by ring)
    _ = 4 * coefficient n * Metric.hausdorffDist (U n) target * ∑ j, w n j := by
        rw [Finset.mul_sum]
    _ ≤ 4 * coefficient n * Metric.hausdorffDist (U n) target :=
        mul_le_of_le_one_right (mul_nonneg (mul_nonneg zero_le_four hc) hd) (hw1 n)

/-- All the finite support defects disappear in the actual selected
limit; their number may grow without bound. -/
theorem selectionDefect_sum_tendsto {target : Set Plane} {U : ℕ → Set Plane}
    (hTarget : IsDownwardCap target) (hU : ∀ n, IsDownwardCap (U n))
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ} (hcoefficient : ∀ n, 0 ≤ coefficient n)
    (hrate : Tendsto coefficient atTop (𝓝 0)) (hHausdorff : CapHausdorffTendsto U target) :
    Tendsto (fun n => ∑ j, selectionDefect target (U n) (level n) (coefficient n) j)
      atTop (𝓝 0) :=
  supportDefect_sum_tendsto hTarget hU hcoefficient hrate (fun n => stageWeight_nonneg (level n))
    (fun n => sum_stageWeight_le_one (level n)) hHausdorff

end AngularGrid

end AmbidextrousSofa
