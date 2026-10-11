module

public import AmbidextrousSofa.Analysis.RegularTangency
public import AmbidextrousSofa.Analysis.SourceLocalization
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

/-!
# Globally visible parts of the actual two-wall niche

Monotonicity of the second tangency abscissa makes its own second wall
a global maximum of that wall family. Monotonicity of the first
tangency abscissa on a future interval gives strict global visibility
of a corner with opposite-signed velocities. These are inequalities
for every angular wall, rather than a prescribed contact chart.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem endpoint_le_of_hasDerivAt_nonneg
    {f d : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (d t) t)
    (hsign : ∀ t ∈ Ioo a b, 0 ≤ d t) : f a ≤ f b :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (HasDerivAt.continuousOn hd) (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    (by rwa [interior_Icc]) (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab

theorem endpoint_lt_of_hasDerivAt_pos
    {f d : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (d t) t)
    (hsign : ∀ t ∈ Ioo a b, 0 < d t) : f a < f b :=
  strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc a b)
    (HasDerivAt.continuousOn hd) (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    (by rwa [interior_Icc]) (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le) hab

theorem endpoint_le_of_hasDerivAt_nonpos
    {f d : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (d t) t)
    (hsign : ∀ t ∈ Ioo a b, d t ≤ 0) : f b ≤ f a :=
  antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
    (HasDerivAt.continuousOn hd) (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    (by rwa [interior_Icc]) (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab

theorem endpoint_lt_of_hasDerivAt_neg
    {f d : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (d t) t)
    (hsign : ∀ t ∈ Ioo a b, d t < 0) : f b < f a :=
  strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc a b)
    (HasDerivAt.continuousOn hd) (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    (by rwa [interior_Icc]) (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le) hab

theorem firstWall_attachedCorner (U : Set Plane) {t : ℝ} (hs : Real.sin t ≠ 0) :
    firstWall U t (attachedCorner U t).1 = (attachedCorner U t).2 := by
  rw [firstWall, div_eq_iff hs]
  dsimp only [attachedCorner]
  linear_combination (1 - support U (unitNormal t)) * Real.sin_sq_add_cos_sq t

theorem secondWall_attachedCorner (U : Set Plane) {t : ℝ} (hc : Real.cos t ≠ 0) :
    secondWall U t (attachedCorner U t).1 = (attachedCorner U t).2 := by
  rw [secondWall, div_eq_iff hc]
  dsimp only [attachedCorner]
  linear_combination (1 - support U (companionNormal t)) * Real.sin_sq_add_cos_sq t

theorem firstWall_firstTangency (U : Set Plane) {t : ℝ} (hs : Real.sin t ≠ 0) :
    firstWall U t (firstTangency U t).1 = (firstTangency U t).2 := by
  have hc := firstWall_attachedCorner U hs
  rw [firstWall, div_eq_iff hs] at hc ⊢
  dsimp only [firstTangency]
  linear_combination hc

theorem secondWall_secondTangency (U : Set Plane) {t : ℝ} (hc : Real.cos t ≠ 0) :
    secondWall U t (secondTangency U t).1 = (secondTangency U t).2 := by
  have hcorner := secondWall_attachedCorner U hc
  rw [secondWall, div_eq_iff hc] at hcorner ⊢
  dsimp only [secondTangency]
  linear_combination hcorner

/-- A nondecreasing tangency abscissa gives a global maximum of the
second-wall family at its own tangency point. -/
theorem secondWall_le_at_secondTangency
    (U : Set Plane)
    (hD : MonotoneOn (fun t => (secondTangency U t).1) (Ioo (0 : ℝ) (Real.pi / 2)))
    (hd : ∀ t ∈ Ioo (0 : ℝ) (Real.pi / 2), ∀ x : ℝ,
      HasDerivAt (fun s => secondWall U s x)
        ((x - (secondTangency U t).1) / Real.cos t ^ 2) t)
    {s t : ℝ} (hs : s ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    secondWall U s (secondTangency U t).1 ≤ (secondTangency U t).2 := by
  rw [← secondWall_secondTangency U
    (sin_cos_pos_of_mem_quarter ht).2.ne']
  rcases le_total s t with hst | hts
  · exact endpoint_le_of_hasDerivAt_nonneg hst
      (fun r hr => hd r ⟨hs.1.trans_le hr.1, hr.2.trans_lt ht.2⟩ _) fun r hr => div_nonneg
        (sub_nonneg.2 (hD ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩ ht hr.2.le)) (sq_nonneg _)
  · exact endpoint_le_of_hasDerivAt_nonpos hts
      (fun r hr => hd r ⟨ht.1.trans_le hr.1, hr.2.trans_lt hs.2⟩ _) fun r hr =>
        div_nonpos_of_nonpos_of_nonneg
          (sub_nonpos.2 (hD ht ⟨ht.1.trans hr.1, hr.2.trans hs.2⟩ hr.1.le)) (sq_nonneg _)

theorem sweptNiche_at_secondTangency {U : Set Plane} (hU : IsDownwardCap U)
    (hD : MonotoneOn (fun t => (secondTangency U t).1) (Ioo (0 : ℝ) (Real.pi / 2)))
    (hd : ∀ t ∈ Ioo (0 : ℝ) (Real.pi / 2), ∀ x : ℝ,
      HasDerivAt (fun s => secondWall U s x)
        ((x - (secondTangency U t).1) / Real.cos t ^ 2) t)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hq : 0 ≤ firstCornerVelocity U t) (hy : 0 ≤ (secondTangency U t).2) :
    sweptNiche U (Real.pi / 2) (secondTangency U t).1 = (secondTangency U t).2 := by
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ht
  -- The first wall exceeds the second tangency point by `firstCornerVelocity / sin`.
  have hfirst : (secondTangency U t).2 ≤ firstWall U t (secondTangency U t).1 := by
    have hcorner := firstWall_attachedCorner U hs.ne'
    rw [firstWall, div_eq_iff hs.ne'] at hcorner
    rw [firstWall, le_div_iff₀ hs]
    dsimp only [secondTangency]
    linarith [congrArg (firstCornerVelocity U t * ·) (Real.sin_sq_add_cos_sq t)]
  refine le_antisymm (sweptNiche_le_of_forall (by positivity) hy fun s hs =>
    (min_le_right _ _).trans (secondWall_le_at_secondTangency U hD hd hs ht)) ?_
  calc (secondTangency U t).2 = cornerWall U t (secondTangency U t).1 := by
        rw [cornerWall, secondWall_secondTangency U hc.ne', min_eq_right hfirst]
    _ ≤ _ := cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCompact le_rfl _) ht

/-- An angle where the clipped wall attains a positive height is interior, and its unclipped
corner wall attains that height. -/
theorem mem_Ioo_and_cornerWall_eq_of_fullWallClip_eq {U : CompactCap} {x y s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) (Real.pi / 2)) (hy : 0 < y) (h : fullWallClip U x s = y) :
    s ∈ Ioo (0 : ℝ) (Real.pi / 2) ∧ cornerWall U.carrier s x = y := by
  refine ⟨⟨hs.1.lt_of_ne ?_, hs.2.lt_of_ne ?_⟩,
    ((max_eq_iff.1 h).resolve_right fun h' => hy.ne h'.1).1⟩ <;> rintro rfl
  · exact hy.ne ((fullWallClip_zero U x).symm.trans h)
  · exact hy.ne ((fullWallClip_pi_div_two U x).symm.trans h)

/-- A maximizing second wall must have its tangency abscissa at the
given physical point. This includes nontrivial tangency plateaus. -/
theorem secondTangency_abscissa_of_maximizing_angle {U : Set Plane}
    (hU : IsDownwardCap U)
    (hD : MonotoneOn (fun t => (secondTangency U t).1) (Ioo (0 : ℝ) (Real.pi / 2)))
    (hd : ∀ t ∈ Ioo (0 : ℝ) (Real.pi / 2), ∀ x : ℝ,
      HasDerivAt (fun s => secondWall U s x)
        ((x - (secondTangency U t).1) / Real.cos t ^ 2) t)
    {s t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hq : 0 ≤ firstCornerVelocity U t) (hy : 0 < (secondTangency U t).2)
    (hs : s ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hmax : fullWallClip hU.toCompactCap (secondTangency U t).1 s =
      sweptNiche U (Real.pi / 2) (secondTangency U t).1) :
    s ∈ Ioo (0 : ℝ) (Real.pi / 2) ∧ (secondTangency U s).1 = (secondTangency U t).1 := by
  obtain ⟨hsq, hcorner⟩ := mem_Ioo_and_cornerWall_eq_of_fullWallClip_eq hs hy
    (hmax.trans (sweptNiche_at_secondTangency hU hD hd ht hq hy.le))
  have hvalue : secondWall U s (secondTangency U t).1 = (secondTangency U t).2 :=
    le_antisymm (secondWall_le_at_secondTangency U hD hd hsq ht)
      (hcorner.ge.trans (min_le_right _ _))
  -- The second wall through the tangency point is locally maximal at `s`.
  have hlocal : IsLocalMax (fun r => secondWall U r (secondTangency U t).1) s :=
    Filter.eventually_of_mem (Ioo_mem_nhds hsq.1 hsq.2) fun r hr =>
      (secondWall_le_at_secondTangency U hD hd hr ht).trans hvalue.ge
  have hx := (div_eq_zero_iff.mp (hlocal.hasDerivAt_eq_zero (hd s hsq _))).resolve_right
    (pow_ne_zero 2 (sin_cos_pos_of_mem_quarter hsq).2.ne')
  exact ⟨hsq, (sub_eq_zero.mp hx).symm⟩

/-- A corner with `p < 0 < q` is a strict global maximizer of the
actual full wall family once the other quarter and the whole future
have their proved monotonicity. -/
theorem sweptNiche_at_visible_corner {U : Set Plane} (hU : IsDownwardCap U)
    {b : ℝ} (hb : 0 ≤ b)
    (hD : MonotoneOn (fun t => (secondTangency U t).1) (Ioo (0 : ℝ) (Real.pi / 2)))
    (hB : MonotoneOn (fun t => (firstTangency U t).1) (Ioo b (Real.pi / 2)))
    (hR : ∀ t ∈ Ioo (0 : ℝ) (Real.pi / 2), ∀ x : ℝ,
      HasDerivAt (fun s => firstWall U s x)
        ((x - (firstTangency U t).1) / Real.sin t ^ 2) t)
    (hS : ∀ t ∈ Ioo (0 : ℝ) (Real.pi / 2), ∀ x : ℝ,
      HasDerivAt (fun s => secondWall U s x)
        ((x - (secondTangency U t).1) / Real.cos t ^ 2) t)
    {t : ℝ} (ht : t ∈ Ioo b (Real.pi / 2))
    (hq : 0 < firstCornerVelocity U t) (hr : 0 < secondCornerVelocity U t)
    (hy : 0 < (attachedCorner U t).2) :
    sweptNiche U (Real.pi / 2) (attachedCorner U t).1 = (attachedCorner U t).2 ∧
      (∀ s ∈ Icc (0 : ℝ) (Real.pi / 2),
        fullWallClip hU.toCompactCap (attachedCorner U t).1 s =
          sweptNiche U (Real.pi / 2) (attachedCorner U t).1 → s = t) := by
  have htq : t ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨hb.trans_lt ht.1, ht.2⟩
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter htq
  have hcorner : cornerWall U t (attachedCorner U t).1 = (attachedCorner U t).2 := by
    rw [cornerWall, firstWall_attachedCorner U hs.ne', secondWall_attachedCorner U hc.ne',
      min_self]
  -- Every other wall angle passes strictly below the corner: an earlier second wall, since the
  -- second tangency abscissa is monotone, and a later first wall, since the first one is.
  have hlt (s : ℝ) (hs' : s ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hne : s ≠ t) :
      cornerWall U s (attachedCorner U t).1 < (attachedCorner U t).2 := by
    rcases hne.lt_or_gt with hst | hts
    · refine (min_le_right _ _).trans_lt ?_
      rw [← secondWall_attachedCorner U hc.ne']
      refine endpoint_lt_of_hasDerivAt_pos hst
        (fun r hri => hS r ⟨hs'.1.trans_le hri.1, hri.2.trans_lt htq.2⟩ _) fun r hri =>
          div_pos ?_ (pow_pos (Real.cos_pos_of_mem_Ioo
            ⟨by linarith [hs'.1, hri.1, Real.pi_pos], hri.2.trans htq.2⟩) 2)
      have hmono := hD ⟨hs'.1.trans hri.1, hri.2.trans htq.2⟩ htq hri.2.le
      have : (secondTangency U t).1 =
        (attachedCorner U t).1 - firstCornerVelocity U t * Real.cos t := rfl
      linarith [mul_pos hq hc]
    · refine (min_le_left _ _).trans_lt ?_
      rw [← firstWall_attachedCorner U hs.ne']
      refine endpoint_lt_of_hasDerivAt_neg hts
        (fun r hri => hR r ⟨htq.1.trans_le hri.1, hri.2.trans_lt hs'.2⟩ _) fun r hri =>
          div_neg_of_neg_of_pos ?_ (pow_pos (Real.sin_pos_of_pos_of_lt_pi (htq.1.trans hri.1)
            (by linarith [hri.2, hs'.2, Real.pi_pos])) 2)
      have hmono := hB ht ⟨ht.1.trans hri.1, hri.2.trans hs'.2⟩ hri.1.le
      have : (firstTangency U t).1 =
        (attachedCorner U t).1 + secondCornerVelocity U t * Real.sin t := rfl
      linarith [mul_pos hr hs]
  have hN : sweptNiche U (Real.pi / 2) (attachedCorner U t).1 = (attachedCorner U t).2 :=
    le_antisymm (sweptNiche_le_of_forall (by positivity) hy.le fun s hs' => by
        rcases eq_or_ne s t with rfl | hne
        exacts [hcorner.le, (hlt s hs' hne).le])
      (hcorner.ge.trans
        (cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCompact le_rfl _) htq))
  refine ⟨hN, fun s hs' hmax => by_contra fun hne => ?_⟩
  obtain ⟨hsq, hcw⟩ := mem_Ioo_and_cornerWall_eq_of_fullWallClip_eq hs' hy (hmax.trans hN)
  exact (hlt s hsq hne).ne hcw

/-- This wrapper derives all global wall and tangency hypotheses from
the actual curvature density on the horizontal regular domain. -/
theorem IsDownwardCap.visible_corner_of_unit_companion_and_future
    {U : Set Plane} (hU : IsDownwardCap U) {ρ : ℝ → ℝ} {C b t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hb : 0 ≤ b)
    (hcompanion : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ (s + Real.pi / 2) ≤ 1)
    (hfuture : ∀ᵐ s ∂volume.restrict (Ioo b (Real.pi / 2)), ρ s ≤ 1)
    (ht : t ∈ Ioo b (Real.pi / 2))
    (hq : 0 < firstCornerVelocity U t) (hr : 0 < secondCornerVelocity U t)
    (hy : 0 < (attachedCorner U t).2) :
    sweptNiche U (Real.pi / 2) (attachedCorner U t).1 = (attachedCorner U t).2 ∧
      (∀ s ∈ Icc (0 : ℝ) (Real.pi / 2),
        fullWallClip hU.toCompactCap (attachedCorner U t).1 s =
          sweptNiche U (Real.pi / 2) (attachedCorner U t).1 → s = t) := by
  have hfull := regularCornerDomain_zero.ge
  have hwall (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) (Real.pi / 2)) (x : ℝ) :=
    hU.hasDerivAt_walls_on_regularCornerDomain hρ hρ0 hρC heq (hfull hs) x
  exact sweptNiche_at_visible_corner hU hb
    (hU.secondTangency_monotoneOn_open_of_unit_density hρ hρ0 hρC heq hfull hcompanion).1
    (hU.firstTangency_monotoneOn_open_of_unit_density hρ hρ0 hρC heq
      (fun s hs => hfull ⟨hb.trans_lt hs.1, hs.2⟩) hfuture).1
    (fun s hs x => (hwall s hs x).1) (fun s hs x => (hwall s hs x).2) ht hq hr hy

end AmbidextrousSofa
