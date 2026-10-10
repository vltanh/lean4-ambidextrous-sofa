module

public import AmbidextrousSofa.Analysis.CoreContactPhase
public import AmbidextrousSofa.Analysis.PositiveWallContacts

@[expose] public section

/-!
# Exclusive source angles above a positive first tangent

The first-wall spatial slope is strictly increasing with its angle.
At a differentiable positive first-tangent contact, a second tangent
would have the opposite slope sign. A corner contact would have an
earlier angle, while lying strictly to the left of that angle's first
tangent. Monotonicity of the first tangent excludes that alternative.
Thus every remaining source over this spatial point is the same
strict first-wall source. The two core endpoint angles are explicit;
the selected joint measure gives each of them zero mass.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem strictMonoOn_firstWallSlope :
    StrictMonoOn (fun t : ℝ => -Real.cos t / Real.sin t)
      (Ioo (0 : ℝ) (Real.pi / 2)) := by
  intro s hs t ht hst
  have hss : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs.1
    (by linarith only [hs.2, Real.pi_pos])
  have hst' : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith only [ht.2, Real.pi_pos])
  have hdiff := Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hst)
    (show t - s < Real.pi by linarith only [ht.2, hs.1, Real.pi_pos])
  rw [Real.sin_sub] at hdiff
  apply (div_lt_div_iff₀ hss hst').mpr
  nlinarith only [hdiff]

section ActualPair

variable {U : Set Plane} (hU : IsFullCapMaximizer U)
  {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

local notation "F" => fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
set_option quotPrecheck false in
local notation "B" => firstTangentPoint (F).f (F).fD
set_option quotPrecheck false in
local notation "Z" => innerCornerPoint (F).f (F).g
set_option quotPrecheck false in
local notation "p" => supportP (F).fD (F).g
set_option quotPrecheck false in
local notation "q" => supportQ (F).gD (F).f
local notation "V" => leftCompanionCap U (horizontalLeft U + capWidth U / 4)

theorem fullTiltedSupportQuarterPair_first_wall_strict_at_first_tangency {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hp : p t < 0) :
    firstWall U t (B t).1 < secondWall U t (B t).1 := by
  have hs : Real.sin t ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith only [ht.2, Real.pi_pos])).ne'
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
  have hgap := fullTiltedSupportQuarterPair_companion_wall_first_tangency_gap
    hU hm haffine hρ hρ0 hρK heq hc.ne'
  have hcut : (B t).2 < secondWall V t (B t).1 := by
    apply sub_pos.mp
    apply (mul_pos_iff_of_pos_right hc).mp
    rw [hgap]
    exact neg_pos.mpr hp
  have hmatch := fullTiltedSupportQuarterPair_first_tangency
    hU hm haffine hρ hρ0 hρK heq ⟨ht.1.le, ht.2⟩
  have hfirst : firstWall U t (B t).1 = (B t).2 := by
    rw [hmatch]
    exact firstWall_firstTangency U hs
  rw [hfirst]
  exact hcut.trans_le (secondWall_mono (leftCompanionCap_subset _ _)
    hU.isCap_fullLeftCompanion.nonempty hU.isCap.isCompact hc _)

theorem fullTiltedSupportQuarterPair_niche_derivative_first_tangency
    (hunit : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ s ≤ 1)
    {t g : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hp : p t < 0) (hy : 0 ≤ (B t).2)
    (hderiv : HasDerivAt (sweptNiche U (Real.pi / 2)) g (B t).1) :
    g = -Real.cos t / Real.sin t := by
  have hniche := fullTiltedSupportQuarterPair_niche_first_tangency
    hU hm haffine hρ hρ0 hρK heq hunit ht hp.le hy
  have hmatch := fullTiltedSupportQuarterPair_first_tangency
    hU hm haffine hρ hρ0 hρK heq ⟨ht.1.le, ht.2⟩
  have hs : Real.sin t ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith only [ht.2, Real.pi_pos])).ne'
  have hcontact : firstWall U t (B t).1 = sweptNiche U (Real.pi / 2) (B t).1 := by
    rw [hniche, hmatch]
    exact firstWall_firstTangency U hs
  exact hU.isCap.niche_derivative_at_strict_first_contact ht hderiv hcontact
    (fullTiltedSupportQuarterPair_first_wall_strict_at_first_tangency
      hU hm haffine hρ hρ0 hρK heq ht hp)

theorem fullTiltedSupportQuarterPair_strict_first_contact_unique
    {C α η t g s : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1) (hmpos : 0 < m)
    (hunit : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ r ≤ 1)
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hp : p t < 0) (hy : 0 < (B t).2)
    (hderiv : HasDerivAt (sweptNiche U (Real.pi / 2)) g (B t).1)
    (hs : s ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hsα : s ≠ α) (hsη : s ≠ η)
    (hmax : fullWallClip hU.isCap.toCompactCap (B t).1 s =
      sweptNiche U (Real.pi / 2) (B t).1) :
    s = t ∧ firstWall U s (B t).1 < secondWall U s (B t).1 := by
  have hniche := fullTiltedSupportQuarterPair_niche_first_tangency
    hU hm haffine hρ hρ0 hρK heq hunit ht hp.le hy.le
  have hpositive : 0 < sweptNiche U (Real.pi / 2) (B t).1 := by
    rw [hniche]
    exact hy
  have hgt := fullTiltedSupportQuarterPair_niche_derivative_first_tangency
    hU hm haffine hρ hρ0 hρK heq hunit ht hp hy.le hderiv
  have hcorner : cornerWall U s (B t).1 = sweptNiche U (Real.pi / 2) (B t).1 :=
    positive_fullWallClip_eq_cornerWall (U := hU.isCap.toCompactCap) hpositive hmax
  rcases lt_trichotomy (firstWall U s (B t).1) (secondWall U s (B t).1)
      with hfirst | htie | hsecond
  · have hcontact : firstWall U s (B t).1 = sweptNiche U (Real.pi / 2) (B t).1 := by
      simpa only [cornerWall, min_eq_left hfirst.le] using hcorner
    have hgs := hU.isCap.niche_derivative_at_strict_first_contact hs hderiv hcontact hfirst
    exact ⟨strictMonoOn_firstWallSlope.injOn hs ht (hgs.symm.trans hgt), hfirst⟩
  · have hfirst : firstWall U s (B t).1 = sweptNiche U (Real.pi / 2) (B t).1 := by
      simpa only [cornerWall, min_eq_left htie.le] using hcorner
    have hpoint := wall_tie_eq_attachedCorner hs hfirst (htie.symm.trans hfirst)
    have hx : (B t).1 = (attachedCorner U s).1 := by rw [← hpoint]
    have hy' : sweptNiche U (Real.pi / 2) (B t).1 = (attachedCorner U s).2 :=
      congrArg Prod.snd hpoint
    have hcontact : sweptNiche U (Real.pi / 2) (attachedCorner U s).1 =
        (attachedCorner U s).2 := by simpa only [hx] using hy'
    have hD : HasDerivAt (sweptNiche U (Real.pi / 2)) g (attachedCorner U s).1 := by
      simpa only [hx] using hderiv
    have hpos : 0 < (attachedCorner U s).2 := by rw [← hy']; exact hpositive
    obtain ⟨hafter, hclosed⟩ :=
      fullTiltedSupportQuarterPair_positive_attachedCorner_contact_mem_closed_core_phase
        hU hm haffine hρ hρ0 hρK heq hl hr hheight hmpos hphase hs hpos hD hcontact
    have hcore : s ∈ Ioo α η :=
      ⟨lt_of_le_of_ne hclosed.1 hsα.symm, lt_of_le_of_ne hclosed.2 hsη⟩
    have hbound := (hU.isCap.niche_derivative_bounds_at_attachedCorner hs hD hcontact).1
    rw [hgt] at hbound
    have hst : s ≤ t := by
      by_contra hnot
      exact (not_lt_of_ge hbound)
        (strictMonoOn_firstWallSlope ht hs (lt_of_not_ge hnot))
    have hmatch := (fullTiltedSupportQuarterPair_other_points_after_affine
      hU hm haffine hρ hρ0 hρK heq ⟨hs.1.le, hs.2⟩ hafter).2
    have hleft : (attachedCorner U s).1 < (B s).1 := by
      rw [← hmatch, innerCorner_fst_eq_firstTangent (F).f (F).g (F).fD]
      have hsin : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs.1
        (by linarith only [hs.2, Real.pi_pos])
      have hprod := mul_neg_of_neg_of_pos (hphase.core_signs s hcore).1 hsin
      linarith only [hprod]
    have horder := (fullTiltedSupportQuarterPair_first_tangent_order
      hU hm haffine hρ hρ0 hρK heq hunit).1
    have hle := horder (Ioo_subset_Icc_self hs) (Ioo_subset_Icc_self ht) hst
    exact False.elim (by linarith only [hleft, hle, hx])
  · have hcontact : secondWall U s (B t).1 = sweptNiche U (Real.pi / 2) (B t).1 := by
      simpa only [cornerWall, min_eq_right hsecond.le] using hcorner
    have hgs := hU.isCap.niche_derivative_at_strict_second_contact hs hderiv hcontact hsecond
    have hsin_s : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs.1
      (by linarith only [hs.2, Real.pi_pos])
    have hcos_s : 0 < Real.cos s := Real.cos_pos_of_mem_Ioo
      ⟨by linarith only [hs.1, Real.pi_pos], hs.2⟩
    have hsin_t : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
      (by linarith only [ht.2, Real.pi_pos])
    have hcos_t : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
      ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
    have hgpos : 0 < g := by rw [hgs]; exact div_pos hsin_s hcos_s
    have hgneg : g < 0 := by
      rw [hgt]
      exact div_neg_of_neg_of_pos (neg_neg_of_pos hcos_t) hsin_t
    exact False.elim (lt_asymm hgpos hgneg)

end ActualPair

end AmbidextrousSofa
