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
top segment. The final theorem chooses its own selected sequence.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace AngularGrid

open FinitePolygon

theorem positive_middle_measure_le_outer_without_top_of_selected
    {target : Set Plane} {U : ℕ → Set Plane} {L R a b : ℝ}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval
      (horizontalLeft target) (horizontalRight target), capRoof target x = m * x + c)
    (hTargetBox : target ⊆ Icc L R ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target L R (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hleft : L < horizontalLeft target) (hright : horizontalRight target < R)
    (ha : (a, 1) ∈ target) (hb : (b, 1) ∈ target) :
    volume.real (middleHalfInterval (horizontalLeft target) (horizontalRight target) ∩
      {x : ℝ | 0 < sweptNiche target (Real.pi / 2) x}) ≤
    volume.real (Icc (horizontalLeft target) (horizontalLeft target + capWidth target / 4) \ Ioo a b) +
      volume.real (Icc (horizontalRight target - capWidth target / 4) (horizontalRight target) \ Ioo a b) := by
  let C : ℝ := 4 * (|L| + |R| + 1) + 12
  let l : ℕ → ℝ := fun n => horizontalLeft (U n)
  let r : ℕ → ℝ := fun n => horizontalRight (U n)
  let jL : ℕ → ℝ := fun n => horizontalLeft (U n) + capWidth (U n) / 4
  let jR : ℕ → ℝ := fun n => horizontalRight (U n) - capWidth (U n) / 4
  let Q : ℝ := volume.real (middleHalfInterval (horizontalLeft target) (horizontalRight target) ∩
    {x : ℝ | 0 < sweptNiche target (Real.pi / 2) x})
  let A : ℝ := volume.real
    (Icc (horizontalLeft target) (horizontalLeft target + capWidth target / 4) \ Ioo a b) +
    volume.real
      (Icc (horizontalRight target - capWidth target / 4) (horizontalRight target) \ Ioo a b)
  have hcap : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have hl := hHausdorff.horizontalLeft_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hTarget.isCap.isCompact hTarget.isCap.nonempty
  have hr := hHausdorff.horizontalRight_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hTarget.isCap.isCompact hTarget.isCap.nonempty
  have horder (n : ℕ) : l n ≤ jL n ∧ jL n ≤ jR n ∧ jR n ≤ r n := by
    have h := horizontalLeft_le_horizontalRight (hcap n).nonempty (hcap n).isCompact
    dsimp only [l, r, jL, jR, capWidth]
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  have hwL (n : ℕ) : Icc (l n) (jL n) ⊆ Icc (l n) (r n) :=
    Icc_subset_Icc_right ((horder n).2.1.trans (horder n).2.2)
  have hwR (n : ℕ) : Icc (jR n) (r n) ⊆ Icc (l n) (r n) :=
    Icc_subset_Icc_left ((horder n).1.trans (horder n).2.1)
  have hproj (n : ℕ) : Icc (l n) (r n) = horizontalProjection (U n) :=
    (horizontalProjection_eq_Icc (hcap n).nonempty (hcap n).isCompact (hcap n).convex).symm
  have hbox (n : ℕ) := (hcap n).projection_subset_Icc_of_box (hU n).inBox
  have hcos := sum_cos_abs_normalizedExposureDefect_tendsto_zero_of_canonical_maximum
    hTarget hheight haffine hTargetBox hU hHausdorff hlevel hc hrate hleft hright
  -- Each angular cutoff `η` costs at most `C * (2 * η)` in the limit.
  have hcutoff (η : ℝ) (hη : η ∈ Ioo (0 : ℝ) (Real.pi / 2)) : Q ≤ A + C * (2 * η) := by
    let E : Set ℝ := Ioo (0 : ℝ) Real.pi \ Icc (Real.pi / 2 - η) (Real.pi / 2 + η)
    have hsin : 0 < Real.sin η :=
      Real.sin_pos_of_pos_of_lt_pi hη.1 (by linarith [hη.2, Real.pi_pos])
    have hE (t : ℝ) (ht : t ∈ E) : 0 ≤ Real.sin t ∧ Real.sin η ≤ |Real.cos t| :=
      ⟨(Real.sin_pos_of_pos_of_lt_pi ht.1.1 ht.1.2).le,
        abs_cos_ge_sin_of_outside_top_interval hη ht.1 ht.2⟩
    have hUL := integral_topRemovedWindowEnvelope_tendsto hHausdorff hcap hTarget.isCap
      (fun n => (hU n).polygon_eq) ha hb hheight hsin hE hl (hl.add ((hr.sub hl).div_const 4))
      (fun n => (hwL n).trans (hproj n).le) fun n => (hwL n).trans (hbox n)
    have hUR := integral_topRemovedWindowEnvelope_tendsto hHausdorff hcap hTarget.isCap
      (fun n => (hU n).polygon_eq) ha hb hheight hsin hE (hr.sub ((hr.sub hl).div_const 4)) hr
      (fun n => (hwR n).trans (hproj n).le) fun n => (hwR n).trans (hbox n)
    have herror : Tendsto (fun n => C * (2 * η + mesh (level n))) atTop (𝓝 (C * (2 * η))) := by
      simpa only [add_zero, Function.comp_apply] using
        (tendsto_const_nhds.add (mesh_tendsto.comp hlevel)).const_mul C
    refine (le_of_tendsto_of_tendsto (integral_positiveNicheOverlap_tendsto hTarget.isCap
      hTargetBox hcap (fun n => (hU n).inBox) hHausdorff hlevel) (((hUL.add hUR).add
        (hcos.div_const (Real.sin η))).add herror) (.of_forall fun n => ?_)).trans_eq
      (by rw [zero_div, add_zero]; rfl)
    have houter := add_le_add
      (integral_horizontalOuterDensity_le_envelope (U n) (dyadic (level n)) E (horder n).1 a b)
      (integral_horizontalOuterDensity_le_envelope (U n) (dyadic (level n)) E (horder n).2.2 a b)
    rw [← horizontalOuterMass_eq_integrals (hcap n)] at houter
    exact (integral_positiveNicheOverlap_le hTarget.isCap _).trans
      ((finitePositiveLength_le_horizontalOuterMass_away_top (hcap n) (by positivity)
        (subset_symmetricBox_of_horizontalBox (hU n).inBox) (level n) hη).trans
          (add_le_add_left (add_le_add_left houter _) _))
  -- Letting the cutoff tend to zero.
  refine ge_of_tendsto (x := 𝓝[>] (0 : ℝ)) ?_ (by
    filter_upwards [Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < Real.pi / 2)] with η hη
      using hcutoff η hη)
  simpa using ((((tendsto_id (x := 𝓝 (0 : ℝ))).const_mul 2).const_mul C).const_add A).mono_left
    nhdsWithin_le_nhds

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
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  have hbox : U ⊆ Icc (horizontalLeft U - 1) (horizontalRight U + 1) ×ˢ Icc (0 : ℝ) 1 :=
    fun p hp => ⟨⟨by linarith [(hU.isCap.fst_mem_Icc hp).1],
      by linarith [(hU.isCap.fst_mem_Icc hp).2]⟩, hU.isCap.inStrip hp⟩
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, -, hHausdorff⟩ :=
    AngularGrid.exists_selected_sequence hU (by linarith) hbox
  exact AngularGrid.positive_middle_measure_le_outer_without_top_of_selected
    hU hheight haffine hbox hV hHausdorff (tendsto_atTop_mono hlevel tendsto_id)
    (fun n => (hc n).le) hrate (by linarith) (by linarith) ha hb

end AmbidextrousSofa
