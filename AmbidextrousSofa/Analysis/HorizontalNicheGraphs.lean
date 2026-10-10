import AmbidextrousSofa.Analysis.HorizontalNicheConfinement

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

theorem secondWall_firstTangency_gap (U : Set Plane) {t : ℝ} (hc : Real.cos t ≠ 0) :
    secondWall U t (firstTangency U t).1 - (firstTangency U t).2 =
      secondCornerVelocity U t / Real.cos t := by
  have hcorner := secondWall_attachedCorner U hc
  rw [secondWall, div_eq_iff hc] at hcorner
  rw [eq_div_iff hc, sub_mul, secondWall, div_mul_cancel₀ _ hc]
  dsimp only [firstTangency]
  nlinarith [congrArg (fun z : ℝ => secondCornerVelocity U t * z)
    (Real.sin_sq_add_cos_sq t)]

theorem firstWall_le_at_firstTangency
    (U : Set Plane)
    (hB : MonotoneOn (fun t => (firstTangency U t).1) (Ioo (0 : ℝ) (Real.pi / 2)))
    (hd : ∀ t ∈ Ioo (0 : ℝ) (Real.pi / 2), ∀ x : ℝ,
      HasDerivAt (fun s => firstWall U s x)
        ((x - (firstTangency U t).1) / Real.sin t ^ 2) t)
    {s t : ℝ} (hs : s ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    firstWall U s (firstTangency U t).1 ≤ (firstTangency U t).2 := by
  have hsin : Real.sin t ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])).ne'
  rw [← firstWall_firstTangency U hsin]
  rcases le_total s t with hst | hts
  · apply endpoint_le_of_hasDerivAt_nonneg hst
      (fun r hr => hd r ⟨hs.1.trans_le hr.1, hr.2.trans_lt ht.2⟩ _)
    intro r hr
    apply div_nonneg _ (sq_nonneg _)
    apply sub_nonneg.mpr
    exact hB ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩ ht hr.2.le
  · apply endpoint_le_of_hasDerivAt_nonpos hts
      (fun r hr => hd r ⟨ht.1.trans_le hr.1, hr.2.trans_lt hs.2⟩ _)
    intro r hr
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    apply sub_nonpos.mpr
    exact hB ht ⟨ht.1.trans hr.1, hr.2.trans hs.2⟩ hr.1.le

theorem sweptNiche_at_firstTangency {U : Set Plane} (hU : IsDownwardCap U)
    (hB : MonotoneOn (fun t => (firstTangency U t).1) (Ioo (0 : ℝ) (Real.pi / 2)))
    (hd : ∀ t ∈ Ioo (0 : ℝ) (Real.pi / 2), ∀ x : ℝ,
      HasDerivAt (fun s => firstWall U s x)
        ((x - (firstTangency U t).1) / Real.sin t ^ 2) t)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hr : 0 ≤ secondCornerVelocity U t) (hy : 0 ≤ (firstTangency U t).2) :
    sweptNiche U (Real.pi / 2) (firstTangency U t).1 = (firstTangency U t).2 := by
  have hs : Real.sin t ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])).ne'
  have hc : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  have hgap := secondWall_firstTangency_gap U hc.ne'
  have hsecond : (firstTangency U t).2 ≤ secondWall U t (firstTangency U t).1 := by
    have hnonneg := div_nonneg hr hc.le
    linarith
  have hcorner : cornerWall U t (firstTangency U t).1 = (firstTangency U t).2 := by
    rw [cornerWall, firstWall_firstTangency U hs, min_eq_left hsecond]
  apply le_antisymm
  · apply sweptNiche_le_of_forall (by linarith [Real.pi_pos]) hy
    intro s hs
    exact (min_le_left _ _).trans (firstWall_le_at_firstTangency U hB hd hs ht)
  · rw [← hcorner]
    exact cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCompact le_rfl _) ht

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
  have hB := hU.isCap.firstTangency_monotoneOn_open_of_unit_density hρ hρ0 hρC heq hsub hfirst
  have hwall := fun s hs x =>
    (hU.isCap.hasDerivAt_walls_on_regularCornerDomain hρ hρ0 hρC heq (hsub hs) x).1
  have hfloor := hU.firstTangency_before_top_endpoint hheight hmiddle hρ hρ0 hρC heq
    (by norm_num : (0 : ℝ) ≤ 0) hfirst ht
  exact sweptNiche_at_firstTangency hU.isCap hB.1 hwall ht hr hfloor.2

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
  have hD := hU.isCap.secondTangency_monotoneOn_open_of_unit_density hρ hρ0 hρC heq hsub hcompanion
  have hwall := fun s hs x =>
    (hU.isCap.hasDerivAt_walls_on_regularCornerDomain hρ hρ0 hρC heq (hsub hs) x).2
  have hfloor := hU.secondTangency_from_top_endpoint hheight hmiddle hρ hρ0 hρC heq hcompanion ht
  exact sweptNiche_at_secondTangency hU.isCap hD.1 hwall ht hq hfloor.2

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
  have hfirst := hunit.mono (fun _ h => h.1)
  have hcompanion := hunit.mono (fun _ h => h.2)
  by_cases hqpos : 0 < firstCornerVelocity U t
  · by_cases hrpos : 0 < secondCornerVelocity U t
    · have hvisible := hU.visible_corner_middle_and_height hheight hmiddle hρ hρ0 hρC heq
        (by norm_num : (0 : ℝ) ≤ 0) hcompanion hfirst ht hqpos hrpos
      exact (hU.isCap.visible_corner_of_unit_companion_and_future hρ hρ0 hρC heq
        (by norm_num : (0 : ℝ) ≤ 0) hcompanion hfirst ht hqpos hrpos hvisible.2.2).1
    · have hrzero : secondCornerVelocity U t = 0 := le_antisymm (le_of_not_gt hrpos) hr
      have hB := hU.sweptNiche_firstTangency_of_unit_density
        hheight hmiddle hρ hρ0 hρC heq hfirst ht hr
      simpa only [firstTangency, hrzero, zero_mul, add_zero, sub_zero] using hB
  · have hqzero : firstCornerVelocity U t = 0 := le_antisymm (le_of_not_gt hqpos) hq
    have hD := hU.sweptNiche_secondTangency_of_unit_density
      hheight hmiddle hρ hρ0 hρC heq hcompanion ht hq
    simpa only [secondTangency, hqzero, zero_mul, sub_zero] using hD

end AmbidextrousSofa
