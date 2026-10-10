import AmbidextrousSofa.Analysis.RegularTangency
import AmbidextrousSofa.Analysis.SourceLocalization
import Mathlib.Analysis.Calculus.LocalExtr.Basic

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
    (hsign : ∀ t ∈ Ioo a b, 0 ≤ d t) : f a ≤ f b := by
  have hm : MonotoneOn f (Icc a b) := monotoneOn_of_deriv_nonneg convex_Icc
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => by
      rw [(hd t (interior_subset ht)).deriv]
      exact hsign t (by simpa only [interior_Icc] using ht))
  exact hm (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab

theorem endpoint_lt_of_hasDerivAt_pos
    {f d : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (d t) t)
    (hsign : ∀ t ∈ Ioo a b, 0 < d t) : f a < f b := by
  have hm : StrictMonoOn f (Icc a b) := strictMonoOn_of_deriv_pos convex_Icc
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => by
      rw [(hd t (interior_subset ht)).deriv]
      exact hsign t (by simpa only [interior_Icc] using ht))
  exact hm (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab

theorem endpoint_le_of_hasDerivAt_nonpos
    {f d : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (d t) t)
    (hsign : ∀ t ∈ Ioo a b, d t ≤ 0) : f b ≤ f a := by
  have h := endpoint_le_of_hasDerivAt_nonneg hab
    (fun t ht => (hd t ht).neg) (fun t ht => neg_nonneg.mpr (hsign t ht))
  linarith

theorem endpoint_lt_of_hasDerivAt_neg
    {f d : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (d t) t)
    (hsign : ∀ t ∈ Ioo a b, d t < 0) : f b < f a := by
  have h := endpoint_lt_of_hasDerivAt_pos hab
    (fun t ht => (hd t ht).neg) (fun t ht => neg_pos.mpr (hsign t ht))
  linarith

theorem firstWall_attachedCorner (U : Set Plane) {t : ℝ} (hs : Real.sin t ≠ 0) :
    firstWall U t (attachedCorner U t).1 = (attachedCorner U t).2 := by
  rw [firstWall, div_eq_iff hs]
  dsimp only [attachedCorner]
  have hcircle := Real.sin_sq_add_cos_sq t
  nlinarith [congrArg (fun z : ℝ => (support U (unitNormal t) - 1) * z) hcircle]

theorem secondWall_attachedCorner (U : Set Plane) {t : ℝ} (hc : Real.cos t ≠ 0) :
    secondWall U t (attachedCorner U t).1 = (attachedCorner U t).2 := by
  rw [secondWall, div_eq_iff hc]
  dsimp only [attachedCorner]
  have hcircle := Real.sin_sq_add_cos_sq t
  nlinarith [congrArg (fun z : ℝ => (support U (companionNormal t) - 1) * z) hcircle]

theorem firstWall_firstTangency (U : Set Plane) {t : ℝ} (hs : Real.sin t ≠ 0) :
    firstWall U t (firstTangency U t).1 = (firstTangency U t).2 := by
  have hc := firstWall_attachedCorner U hs
  rw [firstWall, div_eq_iff hs] at hc ⊢
  dsimp only [firstTangency]
  nlinarith

theorem secondWall_secondTangency (U : Set Plane) {t : ℝ} (hc : Real.cos t ≠ 0) :
    secondWall U t (secondTangency U t).1 = (secondTangency U t).2 := by
  have hcorner := secondWall_attachedCorner U hc
  rw [secondWall, div_eq_iff hc] at hcorner ⊢
  dsimp only [secondTangency]
  nlinarith

theorem firstWall_secondTangency_gap (U : Set Plane) {t : ℝ} (hs : Real.sin t ≠ 0) :
    firstWall U t (secondTangency U t).1 - (secondTangency U t).2 =
      firstCornerVelocity U t / Real.sin t := by
  have hc := firstWall_attachedCorner U hs
  rw [firstWall, div_eq_iff hs] at hc
  rw [eq_div_iff hs, sub_mul, firstWall, div_mul_cancel₀ _ hs]
  dsimp only [secondTangency]
  nlinarith [congrArg (fun z : ℝ => firstCornerVelocity U t * z)
    (Real.sin_sq_add_cos_sq t)]

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
  have hcos : Real.cos t ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩).ne'
  rw [← secondWall_secondTangency U hcos]
  rcases le_total s t with hst | hts
  · apply endpoint_le_of_hasDerivAt_nonneg hst
      (fun r hr => hd r ⟨hs.1.trans_le hr.1, hr.2.trans_lt ht.2⟩ _)
    intro r hr
    apply div_nonneg _ (sq_nonneg _)
    apply sub_nonneg.mpr
    exact hD ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩ ht hr.2.le
  · apply endpoint_le_of_hasDerivAt_nonpos hts
      (fun r hr => hd r ⟨ht.1.trans_le hr.1, hr.2.trans_lt hs.2⟩ _)
    intro r hr
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    apply sub_nonpos.mpr
    exact hD ht ⟨ht.1.trans hr.1, hr.2.trans hs.2⟩ hr.1.le

theorem sweptNiche_at_secondTangency {U : Set Plane} (hU : IsDownwardCap U)
    (hD : MonotoneOn (fun t => (secondTangency U t).1) (Ioo (0 : ℝ) (Real.pi / 2)))
    (hd : ∀ t ∈ Ioo (0 : ℝ) (Real.pi / 2), ∀ x : ℝ,
      HasDerivAt (fun s => secondWall U s x)
        ((x - (secondTangency U t).1) / Real.cos t ^ 2) t)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hq : 0 ≤ firstCornerVelocity U t) (hy : 0 ≤ (secondTangency U t).2) :
    sweptNiche U (Real.pi / 2) (secondTangency U t).1 = (secondTangency U t).2 := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
  have hc : Real.cos t ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩).ne'
  have hgap := firstWall_secondTangency_gap U hs.ne'
  have hfirst : (secondTangency U t).2 ≤ firstWall U t (secondTangency U t).1 := by
    have hnonneg := div_nonneg hq hs.le
    linarith
  have hcorner : cornerWall U t (secondTangency U t).1 = (secondTangency U t).2 := by
    rw [cornerWall, secondWall_secondTangency U hc, min_eq_right hfirst]
  apply le_antisymm
  · apply sweptNiche_le_of_forall (by linarith [Real.pi_pos]) hy
    intro s hs
    exact (min_le_right _ _).trans (secondWall_le_at_secondTangency U hD hd hs ht)
  · rw [← hcorner]
    exact cornerWall_le_sweptNiche
      (sweptWallValues_bddAbove hU.isCompact le_rfl _) ht

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
  have hN := sweptNiche_at_secondTangency hU hD hd ht hq hy.le
  rw [hN] at hmax
  have hs0 : s ≠ 0 := by
    intro heq
    rw [heq, fullWallClip_zero] at hmax
    linarith
  have hsL : s ≠ Real.pi / 2 := by
    intro heq
    rw [heq, fullWallClip_pi_div_two] at hmax
    linarith
  have hsq : s ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), lt_of_le_of_ne hs.2 hsL⟩
  have hvalue : secondWall U s (secondTangency U t).1 = (secondTangency U t).2 := by
    have hmin : (secondTangency U t).2 ≤ cornerWall U s (secondTangency U t).1 := by
      change max (cornerWall U s (secondTangency U t).1) 0 = _ at hmax
      rcases max_choice (cornerWall U s (secondTangency U t).1) 0 with h | h
      · rw [h] at hmax
        exact hmax.ge
      · rw [h] at hmax
        linarith
    exact le_antisymm (secondWall_le_at_secondTangency U hD hd hsq ht)
      (hmin.trans (min_le_right _ _))
  have hlocal : IsLocalMax (fun r => secondWall U r (secondTangency U t).1) s := by
    change ∀ᶠ r in 𝓝 s, secondWall U r (secondTangency U t).1 ≤
      secondWall U s (secondTangency U t).1
    filter_upwards [Ioo_mem_nhds hsq.1 hsq.2] with r hr
    rw [hvalue]
    exact secondWall_le_at_secondTangency U hD hd hr ht
  have hzero := hlocal.hasDerivAt_eq_zero (hd s hsq _)
  have hc : Real.cos s ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hsq.1, Real.pi_pos], hsq.2⟩).ne'
  have hx := (div_eq_zero_iff.mp hzero).resolve_right (pow_ne_zero 2 hc)
  exact ⟨hsq, (sub_eq_zero.mp hx).symm⟩

theorem secondWall_lt_at_corner_before
    (U : Set Plane)
    (hD : MonotoneOn (fun t => (secondTangency U t).1) (Ioo (0 : ℝ) (Real.pi / 2)))
    (hd : ∀ t ∈ Ioo (0 : ℝ) (Real.pi / 2), ∀ x : ℝ,
      HasDerivAt (fun s => secondWall U s x)
        ((x - (secondTangency U t).1) / Real.cos t ^ 2) t)
    {s t : ℝ} (hs : s ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hst : s < t)
    (hq : 0 < firstCornerVelocity U t) :
    secondWall U s (attachedCorner U t).1 < (attachedCorner U t).2 := by
  have hcos : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  rw [← secondWall_attachedCorner U hcos.ne']
  apply endpoint_lt_of_hasDerivAt_pos hst
    (fun r hr => hd r ⟨hs.1.trans_le hr.1, hr.2.trans_lt ht.2⟩ _)
  intro r hr
  have hrq : r ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩
  have hmono := hD hrq ht hr.2.le
  have hgap : 0 < (attachedCorner U t).1 - (secondTangency U t).1 := by
    change 0 < (attachedCorner U t).1 -
      ((attachedCorner U t).1 - firstCornerVelocity U t * Real.cos t)
    nlinarith [mul_pos hq hcos]
  have hcr : Real.cos r ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hrq.1, Real.pi_pos], hrq.2⟩).ne'
  exact div_pos (by linarith) (sq_pos_of_ne_zero hcr)

theorem firstWall_lt_at_corner_after
    (U : Set Plane) {b : ℝ} (hb : 0 ≤ b)
    (hB : MonotoneOn (fun t => (firstTangency U t).1) (Ioo b (Real.pi / 2)))
    (hd : ∀ t ∈ Ioo (0 : ℝ) (Real.pi / 2), ∀ x : ℝ,
      HasDerivAt (fun s => firstWall U s x)
        ((x - (firstTangency U t).1) / Real.sin t ^ 2) t)
    {s t : ℝ} (hs : s ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (ht : t ∈ Ioo b (Real.pi / 2)) (hts : t < s)
    (hr : 0 < secondCornerVelocity U t) :
    firstWall U s (attachedCorner U t).1 < (attachedCorner U t).2 := by
  have hsin : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi (hb.trans_lt ht.1) (by linarith [ht.2, Real.pi_pos])
  rw [← firstWall_attachedCorner U hsin.ne']
  apply endpoint_lt_of_hasDerivAt_neg hts
    (fun r hr => hd r ⟨(hb.trans_lt ht.1).trans_le hr.1, hr.2.trans_lt hs.2⟩ _)
  intro r hrI
  have hrq : r ∈ Ioo b (Real.pi / 2) := ⟨ht.1.trans hrI.1, hrI.2.trans hs.2⟩
  have hmono := hB ht hrq hrI.1.le
  have hgap : (attachedCorner U t).1 - (firstTangency U t).1 < 0 := by
    change (attachedCorner U t).1 -
      ((attachedCorner U t).1 + secondCornerVelocity U t * Real.sin t) < 0
    nlinarith [mul_pos hr hsin]
  have hsr : Real.sin r ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (hb.trans_lt hrq.1) (by linarith [hrq.2, Real.pi_pos])).ne'
  exact div_neg_of_neg_of_pos (by linarith) (sq_pos_of_ne_zero hsr)

theorem cornerWall_lt_at_visible_corner_of_ne
    (U : Set Plane) {b : ℝ} (hb : 0 ≤ b)
    (hD : MonotoneOn (fun t => (secondTangency U t).1) (Ioo (0 : ℝ) (Real.pi / 2)))
    (hB : MonotoneOn (fun t => (firstTangency U t).1) (Ioo b (Real.pi / 2)))
    (hR : ∀ t ∈ Ioo (0 : ℝ) (Real.pi / 2), ∀ x : ℝ,
      HasDerivAt (fun s => firstWall U s x)
        ((x - (firstTangency U t).1) / Real.sin t ^ 2) t)
    (hS : ∀ t ∈ Ioo (0 : ℝ) (Real.pi / 2), ∀ x : ℝ,
      HasDerivAt (fun s => secondWall U s x)
        ((x - (secondTangency U t).1) / Real.cos t ^ 2) t)
    {s t : ℝ} (hs : s ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (ht : t ∈ Ioo b (Real.pi / 2)) (hne : s ≠ t)
    (hq : 0 < firstCornerVelocity U t) (hr : 0 < secondCornerVelocity U t) :
    cornerWall U s (attachedCorner U t).1 < (attachedCorner U t).2 := by
  rcases lt_or_gt_of_ne hne with hst | hts
  · exact (min_le_right _ _).trans_lt
      (secondWall_lt_at_corner_before U hD hS hs ⟨hb.trans_lt ht.1, ht.2⟩ hst hq)
  · exact (min_le_left _ _).trans_lt (firstWall_lt_at_corner_after U hb hB hR hs ht hts hr)

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
  have hs : Real.sin t ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi htq.1 (by linarith [htq.2, Real.pi_pos])).ne'
  have hc : Real.cos t ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [htq.1, Real.pi_pos], htq.2⟩).ne'
  have hcorner : cornerWall U t (attachedCorner U t).1 = (attachedCorner U t).2 := by
    rw [cornerWall, firstWall_attachedCorner U hs, secondWall_attachedCorner U hc, min_self]
  have hN : sweptNiche U (Real.pi / 2) (attachedCorner U t).1 = (attachedCorner U t).2 := by
    apply le_antisymm
    · apply sweptNiche_le_of_forall (by linarith [Real.pi_pos]) hy.le
      intro s hsq
      by_cases heq : s = t
      · subst s
        exact hcorner.le
      · exact (cornerWall_lt_at_visible_corner_of_ne U hb hD hB hR hS hsq ht heq hq hr).le
    · rw [← hcorner]
      exact cornerWall_le_sweptNiche
        (sweptWallValues_bddAbove hU.isCompact le_rfl _) htq
  refine ⟨hN, ?_⟩
  intro s hsc heq
  rw [hN] at heq
  by_contra hst
  by_cases hs0 : s = 0
  · rw [hs0, fullWallClip_zero] at heq
    linarith
  by_cases hsL : s = Real.pi / 2
  · rw [hsL, fullWallClip_pi_div_two] at heq
    linarith
  have hsq : s ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨lt_of_le_of_ne hsc.1 (Ne.symm hs0), lt_of_le_of_ne hsc.2 hsL⟩
  have hstrict := cornerWall_lt_at_visible_corner_of_ne U hb hD hB hR hS hsq ht hst hq hr
  have hmax : fullWallClip hU.toCompactCap (attachedCorner U t).1 s < (attachedCorner U t).2 :=
    max_lt hstrict hy
  exact (ne_of_lt hmax) heq

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
  have hfull : Ioo (0 : ℝ) (Real.pi / 2) ⊆ regularCornerDomain 0 := by
    intro s hs
    simpa only [regularCornerDomain_zero] using hs
  have hsub : Ioo b (Real.pi / 2) ⊆ regularCornerDomain 0 := by
    intro s hs
    exact hfull ⟨hb.trans_lt hs.1, hs.2⟩
  have hD := hU.secondTangency_monotoneOn_open_of_unit_density hρ hρ0 hρC heq hfull hcompanion
  have hB := hU.firstTangency_monotoneOn_open_of_unit_density hρ hρ0 hρC heq hsub hfuture
  have hwall := fun s hs x => hU.hasDerivAt_walls_on_regularCornerDomain hρ hρ0 hρC heq (hfull hs) x
  exact sweptNiche_at_visible_corner hU hb hD.1 hB.1
    (fun s hs x => (hwall s hs x).1) (fun s hs x => (hwall s hs x).2) ht hq hr hy

end AmbidextrousSofa
