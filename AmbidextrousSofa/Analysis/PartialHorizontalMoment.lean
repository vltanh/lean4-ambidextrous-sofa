module

public import AmbidextrousSofa.Analysis.PositivePartialBarrierLimit

@[expose] public section

/-!
# The actual proper horizontal source inequality

For each fixed top cutoff, selected source errors and the mesh vanish.
The cutoff then shrinks while remaining disjoint from the fixed terminal
normal. Thus positive proper-barrier length is bounded by the charged
outer windows outside any actual height-one top segment. The final
wrapper constructs the actual selected polygons itself.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa
namespace PartialGrid

open FinitePolygon AngularGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

theorem positive_middle_measure_le_outer_without_top_of_selected
    {target : Set Plane} {U : ℕ → Set Plane} {L R a b : ℝ}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsJointCapMaximizer target α) (hheight : capHeight target = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval
      (horizontalLeft target) (horizontalRight target), capRoof target x = m * x + c)
    (hTargetBox : target ⊆ Icc L R ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target α hαL L R (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hleft : L < horizontalLeft target) (hright : horizontalRight target < R)
    (ha : (a, 1) ∈ target) (hb : (b, 1) ∈ target) :
    volume.real (middleHalfInterval (horizontalLeft target) (horizontalRight target) ∩
      {x : ℝ | 0 < partialBarrier target α x}) ≤
    volume.real (Icc (horizontalLeft target) (horizontalLeft target + capWidth target / 4) \ Ioo a b) +
      volume.real (Icc (horizontalRight target - capWidth target / 4) (horizontalRight target) \ Ioo a b) := by
  let B : ℝ := |L| + |R| + 1
  let C : ℝ := 8 * B + 24
  let l : ℕ → ℝ := fun n => horizontalLeft (U n)
  let r : ℕ → ℝ := fun n => horizontalRight (U n)
  let jL : ℕ → ℝ := fun n => horizontalLeft (U n) + capWidth (U n) / 4
  let jR : ℕ → ℝ := fun n => horizontalRight (U n) - capWidth (U n) / 4
  let A : ℝ := volume.real
    (Icc (horizontalLeft target) (horizontalLeft target + capWidth target / 4) \ Ioo a b) +
    volume.real (Icc (horizontalRight target - capWidth target / 4) (horizontalRight target) \ Ioo a b)
  have hB : 0 ≤ B := by positivity
  have hcap (n : ℕ) : IsDownwardCap (U n) := (hU n).isCap
  have hl := hHausdorff.horizontalLeft_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hTarget.isCap.isCompact hTarget.isCap.nonempty
  have hr := hHausdorff.horizontalRight_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hTarget.isCap.isCompact hTarget.isCap.nonempty
  have horder (n : ℕ) : l n ≤ jL n ∧ jL n ≤ jR n ∧ jR n ≤ r n := by
    have := horizontalLeft_le_horizontalRight (hcap n).nonempty (hcap n).isCompact
    simp only [l, r, jL, jR, capWidth]
    exact ⟨by linarith, by linarith, by linarith⟩
  have hproj (n : ℕ) :=
    horizontalProjection_eq_Icc (hcap n).nonempty (hcap n).isCompact (hcap n).convex
  have hwindowL (n : ℕ) : Icc (l n) (jL n) ⊆ horizontalProjection (U n) := by
    rw [hproj n]; exact Icc_subset_Icc le_rfl ((horder n).2.1.trans (horder n).2.2)
  have hwindowR (n : ℕ) : Icc (jR n) (r n) ⊆ horizontalProjection (U n) := by
    rw [hproj n]; exact Icc_subset_Icc ((horder n).1.trans (horder n).2.1) le_rfl
  have hbox (n : ℕ) : horizontalProjection (U n) ⊆ Icc L R :=
    image_subset_iff.2 fun p hp => ((hU n).inBox hp).1
  have hpositive := integral_positiveBarrierOverlap_tendsto (α := α) (hαL := hαL) hTarget.isCap
    hTargetBox hcap (fun n => (hU n).inBox) hHausdorff hlevel
  have hcos := sum_cos_abs_normalizedExposureDefect_tendsto_zero_of_canonical_maximum
    hTarget hheight haffine hTargetBox hU hHausdorff hlevel hc hrate hleft hright
  -- the bound with an angular cutoff `η` around the top normal, then `η → 0`
  refine ge_of_tendsto (x := 𝓝[>] (0 : ℝ)) (((by fun_prop : Continuous fun η : ℝ =>
    A + C * (2 * η)).tendsto' 0 A (by simp)).mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min (sub_pos.2 hαL) Real.pi_div_two_pos)] with η hη'
  have hη : η ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨hη'.1, hη'.2.trans_le (min_le_right _ _)⟩
  let E : Set ℝ := Ioo (0 : ℝ) Real.pi \ Icc (Real.pi / 2 - η) (Real.pi / 2 + η)
  have hsin : 0 < Real.sin η :=
    Real.sin_pos_of_pos_of_lt_pi hη.1 (by linarith [hη.2, Real.pi_pos])
  have hE (t : ℝ) (ht : t ∈ E) : 0 ≤ Real.sin t ∧ Real.sin η ≤ |Real.cos t| :=
    ⟨(Real.sin_pos_of_pos_of_lt_pi ht.1.1 ht.1.2).le,
      abs_cos_ge_sin_of_outside_top_interval hη ht.1 ht.2⟩
  have hUL := AngularGrid.integral_topRemovedWindowEnvelope_tendsto
    (grid := fun n => outerGrid α (dyadic (level n))) hHausdorff hcap hTarget.isCap
    (fun n => (hU n).polygon_eq) ha hb hheight hsin hE hl (hl.add ((hr.sub hl).div_const 4))
    hwindowL fun n => (hwindowL n).trans (hbox n)
  have hUR := AngularGrid.integral_topRemovedWindowEnvelope_tendsto
    (grid := fun n => outerGrid α (dyadic (level n))) hHausdorff hcap hTarget.isCap
    (fun n => (hU n).polygon_eq) ha hb hheight hsin hE (hr.sub ((hr.sub hl).div_const 4)) hr
    hwindowR fun n => (hwindowR n).trans (hbox n)
  have hlim := ((hUL.add hUR).add (hcos.div_const (Real.sin η))).add
    ((((mesh_tendsto α).comp hlevel).const_add (2 * η)).const_mul C)
  have := le_of_tendsto_of_tendsto' hpositive hlim fun n =>
    (integral_positiveBarrierOverlap_le hTarget.isCap _).trans
      ((finitePositiveLength_le_horizontalOuterMass_away_top (hcap n) hB
        (subset_symmetricBox_of_horizontalBox (hU n).inBox) (level n) hη
        (hη'.2.trans_le (min_le_left _ _))).trans
      (add_le_add_left (add_le_add_left ((AngularGrid.horizontalOuterMass_eq_integrals (hcap n)
        _ E).trans_le (add_le_add
          (AngularGrid.integral_horizontalOuterDensity_le_envelope (U n) _ E (horder n).1 a b)
          (AngularGrid.integral_horizontalOuterDensity_le_envelope (U n) _ E (horder n).2.2 a b)))
        _) _))
  simpa only [zero_div, add_zero, A, capWidth] using this

end PartialGrid

/-- The actual positive proper-barrier length is bounded by the charged
exterior windows outside any actual top segment. Every selected polygon
and source-limit input is constructed from this joint maximum. -/
theorem IsJointCapMaximizer.positive_partial_middle_measure_le_outer_without_top
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval
      (horizontalLeft U) (horizontalRight U), capRoof U x = m * x + c)
    {a b : ℝ} (ha : (a, 1) ∈ U) (hb : (b, 1) ∈ U) :
    volume.real (middleHalfInterval (horizontalLeft U) (horizontalRight U) ∩
      {x : ℝ | 0 < partialBarrier U α x}) ≤
    volume.real (Icc (horizontalLeft U) (horizontalLeft U + capWidth U / 4) \ Ioo a b) +
      volume.real (Icc (horizontalRight U - capWidth U / 4) (horizontalRight U) \ Ioo a b) := by
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  have hbox : U ⊆ Icc (horizontalLeft U - 1) (horizontalRight U + 1) ×ˢ Icc (0 : ℝ) 1 :=
    fun p hp => by
      have hx : p.1 ∈ Icc (horizontalLeft U) (horizontalRight U) :=
        horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex ▸
          ⟨p, hp, rfl⟩
      exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, hU.isCap.inStrip hp⟩
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, _, hHausdorff⟩ :=
    PartialGrid.exists_selected_sequence ⟨α, hU.angle_mem⟩ hproper hU (by linarith) hbox
  exact (PartialGrid.positive_middle_measure_le_outer_without_top_of_selected
    hU hheight haffine hbox hV hHausdorff (tendsto_atTop_mono hlevel tendsto_id)
    (fun n => (hc n).le) hrate (by linarith) (by linarith) ha hb :)

end AmbidextrousSofa
