module

public import AmbidextrousSofa.Analysis.PositiveNicheLimit

@[expose] public section

/-!
# The actual selected horizontal source inequality

The finite horizontal partition is compared with charged outer sources
away from the top normal. The near-top inner mass tends to zero with the
angular cutoff; the cosine-weighted error tends to zero by the proved
endpoint and erosion laws. Spatial dominated convergence then bounds the
actual positive niche length by the two charged windows outside any actual
top segment. The limit argument is stated for any finite bounds of this
form, so that it also serves proper angles. The final theorem chooses its
own selected sequence.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace AngularGrid

open FinitePolygon

/-- Middle lengths `P n` converging to `Q` and bounded, for every angular cutoff `η` around the
top normal, by the charged outer mass of the polygons, a cosine-weighted error `D n` divided by
`sin η`, and `C * (2 * η + m n)` with `D n` and `m n` tending to zero, are bounded in the limit by
the two charged windows outside any actual top segment. -/
theorem limit_le_outer_without_top {target : Set Plane} {U : ℕ → Set Plane}
    {grid : ℕ → Finset QuarterAngle} (hHausdorff : CapHausdorffTendsto U target)
    (hU : ∀ n, IsDownwardCap (U n)) (hTarget : IsDownwardCap target)
    (hpoly : ∀ n, U n = circumscription (U n) (normal (grid n))) {L R a b : ℝ}
    (hbox : ∀ n, U n ⊆ Icc L R ×ˢ Icc (0 : ℝ) 1) (ha : (a, 1) ∈ target) (hb : (b, 1) ∈ target)
    (hheight : capHeight target = 1) {P D m : ℕ → ℝ} {Q C η₀ : ℝ} (hη₀ : 0 < η₀)
    (hη₀' : η₀ ≤ Real.pi / 2) (hP : Tendsto P atTop (𝓝 Q)) (hD : Tendsto D atTop (𝓝 0))
    (hm : Tendsto m atTop (𝓝 0))
    (hfinite : ∀ η ∈ Ioo 0 η₀, ∀ n, P n ≤ horizontalOuterMass (U n) (grid n)
      (Ioo (0 : ℝ) Real.pi \ Icc (Real.pi / 2 - η) (Real.pi / 2 + η)) + D n / Real.sin η +
        C * (2 * η + m n)) :
    Q ≤ volume.real (Icc (horizontalLeft target) (horizontalLeft target + capWidth target / 4) \
        Ioo a b) +
      volume.real (Icc (horizontalRight target - capWidth target / 4) (horizontalRight target) \
        Ioo a b) := by
  let l : ℕ → ℝ := fun n => horizontalLeft (U n)
  let r : ℕ → ℝ := fun n => horizontalRight (U n)
  let jL : ℕ → ℝ := fun n => horizontalLeft (U n) + capWidth (U n) / 4
  let jR : ℕ → ℝ := fun n => horizontalRight (U n) - capWidth (U n) / 4
  let A : ℝ := volume.real
    (Icc (horizontalLeft target) (horizontalLeft target + capWidth target / 4) \ Ioo a b) +
    volume.real (Icc (horizontalRight target - capWidth target / 4) (horizontalRight target) \
      Ioo a b)
  have hl := hHausdorff.horizontalLeft_tendsto (fun n => (hU n).isCompact)
    (fun n => (hU n).nonempty) hTarget.isCompact hTarget.nonempty
  have hr := hHausdorff.horizontalRight_tendsto (fun n => (hU n).isCompact)
    (fun n => (hU n).nonempty) hTarget.isCompact hTarget.nonempty
  have horder (n : ℕ) : l n ≤ jL n ∧ jL n ≤ jR n ∧ jR n ≤ r n := by
    have := horizontalLeft_le_horizontalRight (hU n).nonempty (hU n).isCompact
    simp only [l, r, jL, jR, capWidth]
    exact ⟨by linarith, by linarith, by linarith⟩
  have hproj (n : ℕ) :=
    horizontalProjection_eq_Icc (hU n).nonempty (hU n).isCompact (hU n).convex
  have hwindowL (n : ℕ) : Icc (l n) (jL n) ⊆ horizontalProjection (U n) := by
    rw [hproj n]; exact Icc_subset_Icc le_rfl ((horder n).2.1.trans (horder n).2.2)
  have hwindowR (n : ℕ) : Icc (jR n) (r n) ⊆ horizontalProjection (U n) := by
    rw [hproj n]; exact Icc_subset_Icc ((horder n).1.trans (horder n).2.1) le_rfl
  have hboxproj (n : ℕ) : horizontalProjection (U n) ⊆ Icc L R :=
    image_subset_iff.2 fun p hp => (hbox n hp).1
  -- the bound with an angular cutoff `η` around the top normal, then `η → 0`
  refine ge_of_tendsto (x := 𝓝[>] (0 : ℝ)) (((by fun_prop : Continuous fun η : ℝ =>
    A + C * (2 * η)).tendsto' 0 A (by simp)).mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [Ioo_mem_nhdsGT hη₀] with η hη
  let E : Set ℝ := Ioo (0 : ℝ) Real.pi \ Icc (Real.pi / 2 - η) (Real.pi / 2 + η)
  have hsin : 0 < Real.sin η :=
    Real.sin_pos_of_pos_of_lt_pi hη.1 (by linarith [hη.2, Real.pi_pos])
  have hE (t : ℝ) (ht : t ∈ E) : 0 ≤ Real.sin t ∧ Real.sin η ≤ |Real.cos t| :=
    ⟨(Real.sin_pos_of_pos_of_lt_pi ht.1.1 ht.1.2).le,
      abs_cos_ge_sin_of_outside_top_interval ⟨hη.1, hη.2.trans_le hη₀'⟩ ht.1 ht.2⟩
  have hUL := integral_topRemovedWindowEnvelope_tendsto hHausdorff hU hTarget hpoly ha hb
    hheight hsin hE hl (hl.add ((hr.sub hl).div_const 4)) hwindowL
    fun n => (hwindowL n).trans (hboxproj n)
  have hUR := integral_topRemovedWindowEnvelope_tendsto hHausdorff hU hTarget hpoly ha hb
    hheight hsin hE (hr.sub ((hr.sub hl).div_const 4)) hr hwindowR
    fun n => (hwindowR n).trans (hboxproj n)
  have := le_of_tendsto_of_tendsto' hP (((hUL.add hUR).add (hD.div_const (Real.sin η))).add
    ((hm.const_add (2 * η)).const_mul C)) fun n => (hfinite η hη n).trans
      (add_le_add_left (add_le_add_left ((horizontalOuterMass_eq_integrals (hU n) _ E).trans_le
        (add_le_add (integral_horizontalOuterDensity_le_envelope (U n) _ E (horder n).1 a b)
          (integral_horizontalOuterDensity_le_envelope (U n) _ E (horder n).2.2 a b))) _) _)
  simpa only [zero_div, add_zero, A, capWidth] using this

end AngularGrid

/-- The horizontal source inequality for an actual canonical full cap
maximizer. The selected polygon sequence and every source error are
constructed and discharged in the proof. -/
theorem IsFullCapMaximizer.positive_middle_measure_le_outer_without_top
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval
      (horizontalLeft U) (horizontalRight U), capRoof U x = m * x + c)
    {a b : ℝ} (ha : (a, 1) ∈ U) (hb : (b, 1) ∈ U) :
    volume.real (middleHalfInterval (horizontalLeft U) (horizontalRight U) ∩
      {x : ℝ | 0 < sweptNiche U (Real.pi / 2) x}) ≤
    volume.real (Icc (horizontalLeft U) (horizontalLeft U + capWidth U / 4) \ Ioo a b) +
      volume.real (Icc (horizontalRight U - capWidth U / 4) (horizontalRight U) \ Ioo a b) := by
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, hH⟩ := hU.exists_selected_polygons
  have hcap n := (hV n).isCap
  exact AngularGrid.limit_le_outer_without_top hH hcap hU.isCap (fun n => (hV n).polygon_eq)
    (fun n => (hV n).inBox) ha hb hheight Real.pi_div_two_pos le_rfl
    (AngularGrid.integral_positiveNicheOverlap_tendsto hU.isCap hU.isCap.subset_slack_box hcap
      (fun n => (hV n).inBox) hH hlevel)
    (AngularGrid.sum_cos_abs_normalizedExposureDefect_tendsto_zero_of_canonical_maximum hU
      hheight haffine hU.isCap.subset_slack_box hV hH hlevel hc hrate (sub_one_lt _)
      (lt_add_one _)) (AngularGrid.mesh_tendsto.comp hlevel) fun η hη n =>
    (AngularGrid.integral_positiveNicheOverlap_le hU.isCap _).trans
      (AngularGrid.finitePositiveLength_le_horizontalOuterMass_away_top (hcap n) (by positivity)
        (subset_symmetricBox_of_horizontalBox (hV n).inBox) (level n) hη)

end AmbidextrousSofa
