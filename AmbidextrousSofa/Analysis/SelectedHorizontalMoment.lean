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
  let B : ℝ := |L| + |R| + 1
  let C : ℝ := 4 * B + 12
  let l : ℕ → ℝ := fun n => horizontalLeft (U n)
  let r : ℕ → ℝ := fun n => horizontalRight (U n)
  let jL : ℕ → ℝ := fun n => horizontalLeft (U n) + capWidth (U n) / 4
  let jR : ℕ → ℝ := fun n => horizontalRight (U n) - capWidth (U n) / 4
  let Q : ℝ := volume.real (middleHalfInterval (horizontalLeft target) (horizontalRight target) ∩
    {x : ℝ | 0 < sweptNiche target (Real.pi / 2) x})
  let A : ℝ := volume.real
    (Icc (horizontalLeft target) (horizontalLeft target + capWidth target / 4) \ Ioo a b) +
    volume.real (Icc (horizontalRight target - capWidth target / 4) (horizontalRight target) \ Ioo a b)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  have hcap : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have hbox : ∀ n, U n ⊆ Icc (-B) B ×ˢ Icc (0 : ℝ) 1 :=
    fun n => subset_symmetricBox_of_horizontalBox (hU n).inBox
  have hl := hHausdorff.horizontalLeft_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hTarget.isCap.isCompact hTarget.isCap.nonempty
  have hr := hHausdorff.horizontalRight_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hTarget.isCap.isCompact hTarget.isCap.nonempty
  have hjL : Tendsto jL atTop (𝓝 (horizontalLeft target + capWidth target / 4)) :=
    hl.add ((hr.sub hl).div_const 4)
  have hjR : Tendsto jR atTop (𝓝 (horizontalRight target - capWidth target / 4)) :=
    hr.sub ((hr.sub hl).div_const 4)
  have horder (n : ℕ) : l n ≤ jL n ∧ jL n ≤ jR n ∧ jR n ≤ r n := by
    have h := horizontalLeft_le_horizontalRight (hcap n).nonempty (hcap n).isCompact
    dsimp [l, r, jL, jR, capWidth]
    constructor
    · linarith
    · constructor <;> linarith
  have hwindowL (n : ℕ) : Icc (l n) (jL n) ⊆ horizontalProjection (U n) := by
    rw [horizontalProjection_eq_Icc (hcap n).nonempty (hcap n).isCompact (hcap n).convex]
    intro x hx
    exact ⟨hx.1, hx.2.trans ((horder n).2.1.trans (horder n).2.2)⟩
  have hwindowR (n : ℕ) : Icc (jR n) (r n) ⊆ horizontalProjection (U n) := by
    rw [horizontalProjection_eq_Icc (hcap n).nonempty (hcap n).isCompact (hcap n).convex]
    intro x hx
    exact ⟨((horder n).1.trans (horder n).2.1).trans hx.1, hx.2⟩
  have hboxL (n : ℕ) : Icc (l n) (jL n) ⊆ Icc L R := by
    intro x hx
    obtain ⟨p, hp, hpx⟩ := hwindowL n hx
    simpa only [hpx] using ((hU n).inBox hp).1
  have hboxR (n : ℕ) : Icc (jR n) (r n) ⊆ Icc L R := by
    intro x hx
    obtain ⟨p, hp, hpx⟩ := hwindowR n hx
    simpa only [hpx] using ((hU n).inBox hp).1
  have hpositive := integral_positiveNicheOverlap_tendsto hTarget.isCap hTargetBox hcap
    (fun n => (hU n).inBox) hHausdorff hlevel
  have hcos := sum_cos_abs_normalizedExposureDefect_tendsto_zero_of_canonical_maximum
    hTarget hheight haffine hTargetBox hU hHausdorff hlevel hc hrate hleft hright
  have hcutoff (η : ℝ) (hη : η ∈ Ioo (0 : ℝ) (Real.pi / 2)) : Q ≤ A + C * (2 * η) := by
    let E : Set ℝ := Ioo (0 : ℝ) Real.pi \ Icc (Real.pi / 2 - η) (Real.pi / 2 + η)
    have hsin : 0 < Real.sin η :=
      Real.sin_pos_of_pos_of_lt_pi hη.1 (by linarith [hη.2, Real.pi_pos])
    have hE (t : ℝ) (ht : t ∈ E) : 0 ≤ Real.sin t ∧ Real.sin η ≤ |Real.cos t| :=
      ⟨(Real.sin_pos_of_pos_of_lt_pi ht.1.1 ht.1.2).le,
        abs_cos_ge_sin_of_outside_top_interval hη ht.1 ht.2⟩
    have hUL := integral_topRemovedWindowEnvelope_tendsto hHausdorff hcap hTarget.isCap
      (fun n => (hU n).polygon_eq) ha hb hheight hsin hE hl hjL hwindowL hboxL
    have hUR := integral_topRemovedWindowEnvelope_tendsto hHausdorff hcap hTarget.isCap
      (fun n => (hU n).polygon_eq) ha hb hheight hsin hE hjR hr hwindowR hboxR
    have herror : Tendsto (fun n => C * (2 * η + mesh (level n))) atTop (𝓝 (C * (2 * η))) := by
      simpa only [add_zero, Function.comp_apply] using
        (tendsto_const_nhds.add (mesh_tendsto.comp hlevel)).const_mul C
    have hbound (n : ℕ) :
        (∫ x in middleHalfInterval (horizontalLeft (U n)) (horizontalRight (U n)),
          positiveNicheOverlap target (U n) (dyadic (level n)) x) ≤
        ((∫ x : ℝ, topRemovedWindowEnvelope (U n) (dyadic (level n)) E (l n) (jL n) a b x) +
          ∫ x : ℝ, topRemovedWindowEnvelope (U n) (dyadic (level n)) E (jR n) (r n) a b x) +
        (∑ j : SourceIndex (dyadic (level n)), |(normal (dyadic (level n)) j).1| *
          |normalizedExposureDefect (U n) (dyadic (level n)) j|) / Real.sin η +
        C * (2 * η + mesh (level n)) := by
      have hfinite := finitePositiveLength_le_horizontalOuterMass_away_top (hcap n) hB
        (hbox n) (level n) hη
      have houter := add_le_add
        (integral_horizontalOuterDensity_le_envelope (U n) (dyadic (level n)) E
          (horder n).1 a b)
        (integral_horizontalOuterDensity_le_envelope (U n) (dyadic (level n)) E
          (horder n).2.2 a b)
      rw [← horizontalOuterMass_eq_integrals (hcap n)] at houter
      exact (integral_positiveNicheOverlap_le hTarget.isCap _).trans
        (hfinite.trans (add_le_add_left (add_le_add_left houter _) _))
    have hlim := ((hUL.add hUR).add (hcos.div_const (Real.sin η))).add herror
    have hineq := le_of_tendsto_of_tendsto hpositive hlim (Eventually.of_forall hbound)
    simpa only [zero_div, add_zero] using hineq
  change Q ≤ A
  by_contra h
  have hgap : 0 < Q - A := sub_pos.mpr (lt_of_not_ge h)
  obtain ⟨η, hη0, hηmax⟩ := exists_between
    (lt_min (show 0 < Real.pi / 2 by linarith [Real.pi_pos])
      (div_pos hgap (show 0 < 4 * C by positivity)))
  have hηL := (lt_min_iff.mp hηmax).1
  have hηgap := (lt_div_iff₀ (show 0 < 4 * C by positivity)).mp (lt_min_iff.mp hηmax).2
  have hineq := hcutoff η ⟨hη0, hηL⟩
  nlinarith [mul_pos hC hη0]

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
  let L := horizontalLeft U - 1
  let R := horizontalRight U + 1
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  have hLR : L ≤ R := by dsimp [L, R]; linarith
  have hbox : U ⊆ Icc L R ×ˢ Icc (0 : ℝ) 1 := by
    intro p hp
    have hx : p.1 ∈ Icc (horizontalLeft U) (horizontalRight U) := by
      rw [← horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex]
      exact ⟨p, hp, rfl⟩
    refine ⟨⟨?_, ?_⟩, hU.isCap.inStrip hp⟩
    · dsimp [L]; linarith [hx.1]
    · dsimp [R]; linarith [hx.2]
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, _, hHausdorff⟩ :=
    AngularGrid.exists_selected_sequence hU hLR hbox
  exact AngularGrid.positive_middle_measure_le_outer_without_top_of_selected
    hU hheight haffine hbox hV hHausdorff (tendsto_atTop_mono hlevel tendsto_id)
    (fun n => (hc n).le) hrate (by dsimp [L]; linarith) (by dsimp [R]; linarith) ha hb

end AmbidextrousSofa
