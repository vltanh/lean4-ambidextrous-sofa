module

public import AmbidextrousSofa.Analysis.HorizontalNicheConfinement

@[expose] public section

/-!
# The three actual niche graphs under unit curvature

Both wall families attain their global maxima at their own tangencies.
The companion sign determines when that maximum is a contact of the
two-wall niche. Standard corners are globally visible, and zero velocity
cases coincide with the corresponding actual tangency. These graph
identities include all endpoint contacts of the eventual sign phases.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem firstWall_le_at_firstTangency
    (U : Set Plane)
    (hB : MonotoneOn (fun t => (firstTangency U t).1) (Ioo (0 : ℝ) (Real.pi / 2)))
    (hd : ∀ t ∈ Ioo (0 : ℝ) (Real.pi / 2), ∀ x : ℝ,
      HasDerivAt (fun s => firstWall U s x)
        ((x - (firstTangency U t).1) / Real.sin t ^ 2) t)
    {s t : ℝ} (hs : s ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    firstWall U s (firstTangency U t).1 ≤ (firstTangency U t).2 := by
  rw [← firstWall_firstTangency U
    (Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])).ne']
  rcases le_total s t with hst | hts
  · exact endpoint_le_of_hasDerivAt_nonneg hst
      (fun r hr => hd r ⟨hs.1.trans_le hr.1, hr.2.trans_lt ht.2⟩ _) fun r hr =>
        div_nonneg (sub_nonneg.mpr (hB ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩ ht hr.2.le))
          (sq_nonneg _)
  · exact endpoint_le_of_hasDerivAt_nonpos hts
      (fun r hr => hd r ⟨ht.1.trans_le hr.1, hr.2.trans_lt hs.2⟩ _) fun r hr =>
        div_nonpos_of_nonpos_of_nonneg
          (sub_nonpos.mpr (hB ht ⟨ht.1.trans hr.1, hr.2.trans hs.2⟩ hr.1.le)) (sq_nonneg _)

theorem IsFullCapMaximizer.sweptNiche_firstTangency_of_unit_density
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C t : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hfirst : ∀ᵐ u ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ u ≤ 1)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hr : 0 ≤ secondCornerVelocity U t) :
    sweptNiche U (Real.pi / 2) (firstTangency U t).1 = (firstTangency U t).2 := by
  have hsub : Ioo (0 : ℝ) (Real.pi / 2) ⊆ regularCornerDomain 0 := by
    rw [regularCornerDomain_zero]
  have hB :=
    (hU.isCap.firstTangency_monotoneOn_open_of_unit_density hρ hρ0 hρC heq hsub hfirst).1
  have hd s (hs : s ∈ Ioo (0 : ℝ) (Real.pi / 2)) x :=
    (hU.isCap.hasDerivAt_walls_on_regularCornerDomain hρ hρ0 hρC heq (hsub hs) x).1
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  have hsecond : (firstTangency U t).2 ≤ secondWall U t (firstTangency U t).1 := by
    have hcorner := secondWall_attachedCorner U hc.ne'
    rw [secondWall, div_eq_iff hc.ne'] at hcorner
    rw [secondWall, le_div_iff₀ hc]
    simp only [firstTangency]
    nlinarith [congrArg (secondCornerVelocity U t * ·) (Real.sin_sq_add_cos_sq t)]
  refine le_antisymm (sweptNiche_le_of_forall (by linarith [Real.pi_pos])
    (hU.firstTangency_before_top_endpoint hheight hmiddle hρ hρ0 hρC heq le_rfl hfirst ht).2
    fun s hs => (min_le_left _ _).trans (firstWall_le_at_firstTangency U hB hd hs ht)) ?_
  calc (firstTangency U t).2 = cornerWall U t (firstTangency U t).1 := by
        rw [cornerWall, firstWall_firstTangency U (Real.sin_pos_of_pos_of_lt_pi ht.1
          (by linarith [ht.2, Real.pi_pos])).ne', min_eq_left hsecond]
    _ ≤ _ := cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCap.isCompact le_rfl _) ht

theorem IsFullCapMaximizer.sweptNiche_secondTangency_of_unit_density
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C t : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hcompanion : ∀ᵐ u ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ (u + Real.pi / 2) ≤ 1)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hq : 0 ≤ firstCornerVelocity U t) :
    sweptNiche U (Real.pi / 2) (secondTangency U t).1 = (secondTangency U t).2 := by
  have hsub : Ioo (0 : ℝ) (Real.pi / 2) ⊆ regularCornerDomain 0 := by
    rw [regularCornerDomain_zero]
  exact sweptNiche_at_secondTangency hU.isCap
    (hU.isCap.secondTangency_monotoneOn_open_of_unit_density hρ hρ0 hρC heq hsub hcompanion).1
    (fun s hs x => (hU.isCap.hasDerivAt_walls_on_regularCornerDomain hρ hρ0 hρC heq
      (hsub hs) x).2) ht hq
    (hU.secondTangency_from_top_endpoint hheight hmiddle hρ hρ0 hρC heq hcompanion ht).2

theorem IsFullCapMaximizer.sweptNiche_corner_of_unit_density
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C t : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hunit : ∀ᵐ u ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      ρ u ≤ 1 ∧ ρ (u + Real.pi / 2) ≤ 1)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hq : 0 ≤ firstCornerVelocity U t) (hr : 0 ≤ secondCornerVelocity U t) :
    sweptNiche U (Real.pi / 2) (attachedCorner U t).1 = (attachedCorner U t).2 := by
  have hfirst := hunit.mono fun _ h => h.1
  have hcompanion := hunit.mono fun _ h => h.2
  rcases hq.lt_or_eq with hqpos | hqzero
  · rcases hr.lt_or_eq with hrpos | hrzero
    · exact (hU.isCap.visible_corner_of_unit_companion_and_future hρ hρ0 hρC heq le_rfl
        hcompanion hfirst ht hqpos hrpos (hU.visible_corner_middle_and_height hheight hmiddle
          hρ hρ0 hρC heq le_rfl hcompanion hfirst ht hqpos hrpos).2.2).1
    · simpa [firstTangency, ← hrzero] using
        hU.sweptNiche_firstTangency_of_unit_density hheight hmiddle hρ hρ0 hρC heq hfirst ht hr
  · simpa [secondTangency, ← hqzero] using hU.sweptNiche_secondTangency_of_unit_density
      hheight hmiddle hρ hρ0 hρC heq hcompanion ht hq

end AmbidextrousSofa
