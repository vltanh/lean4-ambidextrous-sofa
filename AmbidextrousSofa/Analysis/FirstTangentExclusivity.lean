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

namespace AmbidextrousSofa

theorem strictMonoOn_firstWallSlope :
    StrictMonoOn (fun t : ℝ => -Real.cos t / Real.sin t)
      (Ioo (0 : ℝ) (Real.pi / 2)) := by
  intro s hs t ht hst
  have hdiff := Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hst) (by linarith [ht.2, hs.1])
  rw [Real.sin_sub] at hdiff
  apply (div_lt_div_iff₀ (quarter_sin_cos_pos hs).1 (quarter_sin_cos_pos ht).1).mpr
  linarith

section ActualPair

variable {U : Set Plane} (hU : IsFullCapMaximizer U)
  {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

open scoped ActualPair

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
  obtain ⟨hsins, hcoss⟩ := quarter_sin_cos_pos hs
  obtain ⟨hsint, hcost⟩ := quarter_sin_cos_pos ht
  have hniche := fullTiltedSupportQuarterPair_niche_first_tangency
    hU hm haffine hρ hρ0 hρK heq hunit ht hp.le hy.le
  -- At `t` the first wall is a strict contact: the companion wall lies strictly above.
  obtain ⟨hfirst, hgap⟩ :=
    fullTiltedSupportQuarterPair_first_wall_tangency hU hm haffine hρ hρ0 hρK heq ht
  have hgt := hU.isCap.niche_derivative_at_strict_first_contact ht hderiv
    (hfirst.trans hniche.symm) (hfirst ▸ sub_pos.mp ((mul_pos_iff_of_pos_right hcost).mp
      ((neg_pos.mpr hp).trans_le hgap)))
  have hcorner : cornerWall U s (B t).1 = sweptNiche U (Real.pi / 2) (B t).1 :=
    positive_fullWallClip_eq_cornerWall (U := hU.isCap.toCompactCap) (hniche ▸ hy) hmax
  rcases le_or_gt (firstWall U s (B t).1) (secondWall U s (B t).1) with hle | hsecond
  · have hcontact : firstWall U s (B t).1 = sweptNiche U (Real.pi / 2) (B t).1 := by
      rwa [cornerWall, min_eq_left hle] at hcorner
    rcases hle.lt_or_eq with hlt | htie
    · exact ⟨strictMonoOn_firstWallSlope.injOn hs ht
        ((hU.isCap.niche_derivative_at_strict_first_contact hs hderiv hcontact hlt).symm.trans
          hgt), hlt⟩
    -- A tie is an attached corner contact in the core phase, left of the first tangent.
    obtain ⟨hx, hy'⟩ := Prod.ext_iff.mp
      (wall_tie_eq_attachedCorner hs hcontact (htie.symm.trans hcontact)).symm
    have hD : HasDerivAt (sweptNiche U (Real.pi / 2)) g (attachedCorner U s).1 := hx ▸ hderiv
    have hcontact' : sweptNiche U (Real.pi / 2) (attachedCorner U s).1 =
        (attachedCorner U s).2 := by rw [hx, hy']
    obtain ⟨hafter, hclosed⟩ :=
      fullTiltedSupportQuarterPair_positive_attachedCorner_contact_mem_closed_core_phase
        hU hm haffine hρ hρ0 hρK heq hl hr hheight hmpos hphase hs
        (by rw [hy', hniche]; exact hy) hD hcontact'
    have hbound := (hU.isCap.niche_derivative_bounds_at_attachedCorner hs hD hcontact').1
    rw [hgt] at hbound
    have hst : s ≤ t := not_lt.mp fun h => hbound.not_gt (strictMonoOn_firstWallSlope ht hs h)
    have hfst := innerCorner_fst_eq_firstTangent (F).f (F).g (F).fD s
    rw [(fullTiltedSupportQuarterPair_other_points_after_affine
      hU hm haffine hρ hρ0 hρK heq ⟨hs.1.le, hs.2⟩ hafter).2] at hfst
    have hprod := mul_neg_of_neg_of_pos (hphase.core_signs s
      ⟨lt_of_le_of_ne hclosed.1 hsα.symm, lt_of_le_of_ne hclosed.2 hsη⟩).1 hsins
    have hle := (fullTiltedSupportQuarterPair_first_tangent_order
      hU hm haffine hρ hρ0 hρK heq hunit).1 (Ioo_subset_Icc_self hs) (Ioo_subset_Icc_self ht) hst
    linarith only [hprod, hle, hfst, hx]
  -- A strict second-wall contact would have positive slope.
  have hcontact : secondWall U s (B t).1 = sweptNiche U (Real.pi / 2) (B t).1 := by
    rwa [cornerWall, min_eq_right hsecond.le] at hcorner
  have hgs := hU.isCap.niche_derivative_at_strict_second_contact hs hderiv hcontact hsecond
  linarith only [hgs, hgt, div_pos hsins hcoss, div_neg_of_neg_of_pos (neg_neg_of_pos hcost) hsint]

end ActualPair

end AmbidextrousSofa
