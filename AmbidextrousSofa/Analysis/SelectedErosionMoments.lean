module

public import AmbidextrousSofa.Analysis.SelectedPressureLimit

@[expose] public section

/-!
# Selected erosion moments and their vanishing errors

The finite source defect is an actual middle source length minus the two
charged exterior source lengths. Dividing by the vertical normal component
turns those lengths into the outward support derivatives. The selected
curvature inequality therefore bounds that quotient from below.

Horizontal erosion multiplies the quotient by a positive part of the
horizontal normal component. That multiplier is at most one: the total
moment error is bounded by the already summable support penalty errors,
without a singular factor near either horizontal axis. The finite and
limiting translation identities retain both endpoint pressures. The limit
argument holds for every selected limit whose normalized exposure defects
have vanishing lower bounds.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace FinitePolygon

/-- Exposure defects bounded below by nonnegative errors bound both erosion moments below:
the horizontal multipliers lie between zero and one. -/
theorem IsSelected.erosionMoments_ge {ι : Type*} [Fintype ι] {normal : ι → Plane}
    {corners : List (ι × ι)} {terminal : Option ι} {weight : ι → ℝ} {target U : Set Plane}
    {a b c : ℝ} (hU : IsSelected normal corners terminal weight target a b c U) {D : ι → ℝ}
    (hD : ∀ j, 0 ≤ D j)
    (hDle : ∀ j, -D j ≤ finiteExposureDefect U normal corners terminal j / (normal j).2) :
    -(∑ j, D j) ≤ finiteRightMoment U normal corners terminal ∧
      -(∑ j, D j) ≤ finiteLeftMoment U normal corners terminal := by
  have key (m : ι → ℝ) (hm : ∀ j, 0 ≤ m j ∧ m j ≤ 1) : -(∑ j, D j) ≤
      ∑ j, finiteExposureDefect U normal corners terminal j * (m j / (normal j).2) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← mul_div_assoc, mul_div_right_comm]
    linarith [mul_le_mul_of_nonneg_right (hDle j) (hm j).1, mul_le_of_le_one_right (hD j) (hm j).2]
  rw [finiteRightMoment_eq_sum, finiteLeftMoment_eq_sum]
  refine ⟨key _ fun j => ⟨le_max_right _ _, max_le ?_ zero_le_one⟩,
    key _ fun j => ⟨le_max_right _ _, max_le ?_ zero_le_one⟩⟩ <;>
  obtain ⟨θ, hθ⟩ := hU.normal_unit j <;> rw [hθ]
  exacts [Real.cos_le_one θ, neg_le.2 (Real.neg_one_le_cos θ)]

/-- A curvature atom bounded by the middle inner and outer source masses plus a defect `D`, whose
total outer source mass is the atom, bounds the exposure balance below by `-D`. -/
theorem neg_le_exposure_of_atom_le {inner outer : ℝ → ℝ} {l r atom D : ℝ}
    (hint : ∀ s t, IntervalIntegrable outer volume s t)
    (hatom : atom ≤ (∫ x in (l + (r - l) / 4)..(r - (r - l) / 4), inner x) +
      (∫ x in (l + (r - l) / 4)..(r - (r - l) / 4), outer x) + D)
    (hfull : (∫ x in l..r, outer x) = atom) :
    -D ≤ (∫ x in (l + (r - l) / 4)..(r - (r - l) / 4), inner x) -
      (∫ x in l..(l + (r - l) / 4), outer x) - ∫ x in (r - (r - l) / 4)..r, outer x := by
  linarith [intervalIntegral.integral_add_adjacent_intervals (hint l (l + (r - l) / 4))
      (hint _ (r - (r - l) / 4)),
    intervalIntegral.integral_add_adjacent_intervals (hint l (r - (r - l) / 4)) (hint _ r)]

/-- The limit argument for two moments squeezed between vanishing lower bounds and upper bounds
with the given limits, whose differences agree. -/
private theorem erosion_limits {R L uR uL d : ℕ → ℝ} {p q : ℝ} (hpq : 0 ≤ p + q)
    (huR : Tendsto uR atTop (𝓝 (max p 0 - p))) (huL : Tendsto uL atTop (𝓝 (max q 0 - q)))
    (hd : Tendsto d atTop (𝓝 0)) (hR : ∀ n, -d n ≤ R n) (hL : ∀ n, -d n ≤ L n)
    (hRu : ∀ᶠ n in atTop, R n ≤ uR n) (hLu : ∀ᶠ n in atTop, L n ≤ uL n)
    (hbalance : ∀ n, uR n - uL n = R n - L n) :
    Tendsto R atTop (𝓝 (max (-p) 0)) ∧ Tendsto L atTop (𝓝 (max (-q) 0)) := by
  have hpos (y : ℝ) : max y 0 - y = max (-y) 0 := by
    linarith [max_zero_sub_max_neg_zero_eq_self y]
  rw [hpos] at huR huL
  have hdiff := (huR.sub huL).congr hbalance
  have hd' : Tendsto (fun n => -d n) atTop (𝓝 0) := by simpa using hd.neg
  rcases le_total 0 p with hp | hp
  · rw [max_eq_right (neg_nonpos.2 hp)] at huR hdiff ⊢
    have hR0 := tendsto_of_tendsto_of_tendsto_of_le_of_le' hd' huR (.of_forall hR) hRu
    exact ⟨hR0, by simpa using hR0.sub hdiff⟩
  · rw [max_eq_right (neg_nonpos.2 (by linarith : 0 ≤ q))] at huL hdiff ⊢
    have hL0 := tendsto_of_tendsto_of_tendsto_of_le_of_le' hd' huL (.of_forall hL) hLu
    exact ⟨by simpa using hdiff.add hL0, hL0⟩

/-- Both selected erosion moments converge to the exact endpoint defects, given vanishing
nonnegative lower bounds `D` of the normalized exposure defects. At least one pressure is
nonnegative because their sum is the average of two nonnegative roof-plus-barrier heights. That
side has zero limiting moment; translation balance determines the other side as well. No
convergence of the target's endpoint face heights is used. -/
theorem SelectedLimit.erosionMoments_tendsto {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {normal : ∀ n, ι n → Plane} {corners : ∀ n, List (ι n × ι n)} {terminal : ∀ n, Option (ι n)}
    {weight : ∀ n, ι n → ℝ} {target : Set Plane} {a b : ℝ} {c : ℕ → ℝ} {N : ℝ → ℝ}
    {U : ℕ → Set Plane} (hS : SelectedLimit normal corners terminal weight target a b c N U)
    (hN : ∀ x, 0 ≤ N x) {D : ∀ n, ι n → ℝ} (hD : ∀ n j, 0 ≤ D n j)
    (hDle : ∀ n j, -D n j ≤
      finiteExposureDefect (U n) (normal n) (corners n) (terminal n) j / (normal n j).2)
    (hDsum : Tendsto (fun n => ∑ j, D n j) atTop (𝓝 0))
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b) :
    Tendsto (fun n => finiteRightMoment (U n) (normal n) (corners n) (terminal n)) atTop
      (𝓝 (max (-rightEndpointPressure (capRoof target) N (horizontalLeft target)
        (horizontalRight target)) 0)) ∧
    Tendsto (fun n => finiteLeftMoment (U n) (normal n) (corners n) (terminal n)) atTop
      (𝓝 (max (-leftEndpointPressure (capRoof target) N (horizontalLeft target)
        (horizontalRight target)) 0)) := by
  have he := endpointSelectionError_tendsto a b hS.coefficient_tendsto
  have hbounds := hS.eventually_one_le_capWidth.mono fun n hW =>
    (hS.selected n).inward_bounds hS.target_cap hS.target_box hW
  refine erosion_limits (hS.target_cap.endpointPressure_sum_nonneg hN)
    (by simpa only [add_zero] using ((hS.right_height_tendsto hright).sub
      hS.pressures_tendsto.1).add he)
    (by simpa only [add_zero] using ((hS.left_height_tendsto hleft).sub
      hS.pressures_tendsto.2).add he) hDsum
    (fun n => ((hS.selected n).erosionMoments_ge (hD n) (hDle n)).1)
    (fun n => ((hS.selected n).erosionMoments_ge (hD n) (hDle n)).2)
    (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2.1) fun n => ?_
  rw [finite_erosion_moment_balance (hS.isCap n) _ (hS.selected n).normal_snd_pos
    (hS.selected n).slope_injective (hS.selected n).polygon_eq]
  ring

end FinitePolygon

namespace AngularGrid

open FinitePolygon

theorem finiteExposureDefect_div_eq_integrals {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (j : SourceIndex grid) :
    finiteExposureDefect U (normal grid) (pairList grid) none j / (normal grid j).2 =
      (∫ x in (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)..
        (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4),
        innerDensity U grid j x) -
      (∫ x in (horizontalLeft U)..
        (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4),
        outerDensity U grid j x) -
      (∫ x in (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4)..
        (horizontalRight U), outerDensity U grid j x) := by
  classical
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  unfold innerDensity outerDensity finiteExposureDefect WallExpr.sourceMass
  repeat rw [integral_sourceDensity_outward _ _ _ _ (by linarith)]
  ring

/-- Actual curvature and the retained middle facet give the outward
derivative bound even when the selected outer facet has zero length. -/
theorem IsSelectedPolygon.exposure_defect_div_ge {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hc : 0 ≤ coefficient)
    (j : SourceIndex (dyadic level)) :
    -selectionDefect target U level coefficient j ≤
      finiteExposureDefect U (normal (dyadic level)) (pairList (dyadic level)) none j /
        (normal (dyadic level) j).2 := by
  rw [finiteExposureDefect_div_eq_integrals hU.isCap]
  exact neg_le_exposure_of_atom_le (intervalIntegrable_outerDensity U _ j)
    (hU.curvature_atom_le hc j) (integral_outerSource_eq_curvature_atom hU.isCap _
      (normal_snd_pos _) (wallSlopes_injective _) hU.polygon_eq j (normal_eq_unitNormal _ j))

end AngularGrid

end AmbidextrousSofa
