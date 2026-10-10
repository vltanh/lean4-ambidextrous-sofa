module

public import AmbidextrousSofa.Analysis.WallVisibility
public import AmbidextrousSofa.Analysis.RegularCorner
public import Mathlib.Analysis.Calculus.DerivativeTest

@[expose] public section

/-!
# The actual positive wall contacts

A strictly active first wall is stationary at its first tangent, and a
strictly active companion wall is stationary at its second tangent.
Equal walls meet at the literal attached corner. On the strict companion
branch the second-derivative test also forces companion curvature at
most one. The corner branch includes ties, so no tangent coefficient is
assigned to a coincident core point by convention.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

/-- A local maximum has nonpositive second derivative whenever the
first function is continuous. A nonexistent derivative has value zero,
as usual; a positive value would imply a local minimum and hence local
constancy, contradicting that positive value. -/
theorem second_deriv_nonpos_of_isLocalMax {f : ℝ → ℝ} {t : ℝ}
    (hmax : IsLocalMax f t) (hc : ContinuousAt f t) : deriv (deriv f) t ≤ 0 := by
  by_contra hnot
  have hpos : 0 < deriv (deriv f) t := lt_of_not_ge hnot
  have hmin := isLocalMin_of_deriv_deriv_pos hpos hmax.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 t] (fun _ => f t) := by
    change (∀ᶠ s in 𝓝 t, f s ≤ f t) at hmax
    change (∀ᶠ s in 𝓝 t, f t ≤ f s) at hmin
    filter_upwards [hmax, hmin] with s hs ht
    exact le_antisymm hs ht
  have hz : deriv (deriv f) t = 0 := by
    simpa only [deriv_const', deriv_const] using heq.deriv.deriv_eq
  exact hpos.ne' hz

theorem positive_fullWallClip_eq_cornerWall {U : CompactCap} {t x : ℝ}
    (hy : 0 < sweptNiche U (Real.pi / 2) x)
    (hmax : fullWallClip U x t = sweptNiche U (Real.pi / 2) x) :
    cornerWall U t x = sweptNiche U (Real.pi / 2) x := by
  change max (cornerWall U t x) 0 = _ at hmax
  rcases max_choice (cornerWall U t x) 0 with heq | heq
  · rwa [heq] at hmax
  · rw [heq] at hmax
    exact False.elim (hy.ne' hmax.symm)

theorem wall_tie_eq_attachedCorner {U : Set Plane} {t x y : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hfirst : firstWall U t x = y) (hsecond : secondWall U t x = y) :
    (x, y) = attachedCorner U t := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith only [ht.2, Real.pi_pos])
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
  have hw : firstWall U t x = secondWall U t x := hfirst.trans hsecond.symm
  have hx : x = (attachedCorner U t).1 := le_antisymm
    ((secondWall_le_firstWall_iff hs hc).mp hw.ge)
    ((firstWall_le_secondWall_iff hs hc).mp hw.le)
  apply Prod.ext hx
  calc
    y = firstWall U t x := hfirst.symm
    _ = firstWall U t (attachedCorner U t).1 := by rw [hx]
    _ = (attachedCorner U t).2 := firstWall_attachedCorner U hs.ne'

section ActualDensity

variable {U : Set Plane} (hU : IsDownwardCap U) {m K : ℝ} {ρ : ℝ → ℝ}
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

theorem IsDownwardCap.firstWall_isLocalMax_of_strict_contact {t x : ℝ}
    (ht : t ∈ regularCornerDomain m)
    (hcontact : firstWall U t x = sweptNiche U (Real.pi / 2) x)
    (hstrict : firstWall U t x < secondWall U t x) :
    IsLocalMax (fun s => firstWall U s x) t := by
  have hd := hU.hasDerivAt_walls_on_regularCornerDomain hρ hρ0 hρK heq ht x
  have hgap := hd.1.continuousAt.tendsto.eventually_lt hd.2.continuousAt.tendsto hstrict
  change ∀ᶠ s in 𝓝 t, firstWall U s x ≤ firstWall U t x
  filter_upwards [hgap, Ioo_mem_nhds ht.1.1 ht.1.2] with s hs hsI
  rw [hcontact]
  have hwall := cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCompact le_rfl x) hsI
  simpa only [cornerWall, min_eq_left hs.le] using hwall

theorem IsDownwardCap.secondWall_isLocalMax_of_strict_contact {t x : ℝ}
    (ht : t ∈ regularCornerDomain m)
    (hcontact : secondWall U t x = sweptNiche U (Real.pi / 2) x)
    (hstrict : secondWall U t x < firstWall U t x) :
    IsLocalMax (fun s => secondWall U s x) t := by
  have hd := hU.hasDerivAt_walls_on_regularCornerDomain hρ hρ0 hρK heq ht x
  have hgap := hd.2.continuousAt.tendsto.eventually_lt hd.1.continuousAt.tendsto hstrict
  change ∀ᶠ s in 𝓝 t, secondWall U s x ≤ secondWall U t x
  filter_upwards [hgap, Ioo_mem_nhds ht.1.1 ht.1.2] with s hs hsI
  rw [hcontact]
  have hwall := cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCompact le_rfl x) hsI
  simpa only [cornerWall, min_eq_right hs.le] using hwall

theorem IsDownwardCap.first_strict_contact_eq_tangency {t x : ℝ}
    (ht : t ∈ regularCornerDomain m)
    (hcontact : firstWall U t x = sweptNiche U (Real.pi / 2) x)
    (hstrict : firstWall U t x < secondWall U t x) :
    (x, sweptNiche U (Real.pi / 2) x) = firstTangency U t := by
  have hd := (hU.hasDerivAt_walls_on_regularCornerDomain hρ hρ0 hρK heq ht x).1
  have hz := (hU.firstWall_isLocalMax_of_strict_contact hρ hρ0 hρK heq
    ht hcontact hstrict).hasDerivAt_eq_zero hd
  have hs : Real.sin t ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi ht.1.1
    (by linarith only [ht.1.2, Real.pi_pos])).ne'
  have hx : x = (firstTangency U t).1 :=
    sub_eq_zero.mp ((div_eq_zero_iff.mp hz).resolve_right (pow_ne_zero 2 hs))
  apply Prod.ext hx
  calc
    sweptNiche U (Real.pi / 2) x = firstWall U t x := hcontact.symm
    _ = firstWall U t (firstTangency U t).1 := by rw [hx]
    _ = (firstTangency U t).2 := firstWall_firstTangency U hs

theorem IsDownwardCap.second_strict_contact_eq_tangency {t x : ℝ}
    (ht : t ∈ regularCornerDomain m)
    (hcontact : secondWall U t x = sweptNiche U (Real.pi / 2) x)
    (hstrict : secondWall U t x < firstWall U t x) :
    (x, sweptNiche U (Real.pi / 2) x) = secondTangency U t := by
  have hd := (hU.hasDerivAt_walls_on_regularCornerDomain hρ hρ0 hρK heq ht x).2
  have hz := (hU.secondWall_isLocalMax_of_strict_contact hρ hρ0 hρK heq
    ht hcontact hstrict).hasDerivAt_eq_zero hd
  have hc : Real.cos t ≠ 0 := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1.1, Real.pi_pos], ht.1.2⟩).ne'
  have hx : x = (secondTangency U t).1 :=
    sub_eq_zero.mp ((div_eq_zero_iff.mp hz).resolve_right (pow_ne_zero 2 hc))
  apply Prod.ext hx
  calc
    sweptNiche U (Real.pi / 2) x = secondWall U t x := hcontact.symm
    _ = secondWall U t (secondTangency U t).1 := by rw [hx]
    _ = (secondTangency U t).2 := secondWall_secondTangency U hc

/-- Strict tangent and equal-wall corner alternatives are disjoint.
This is the first-family classification of the literal source support. -/
theorem IsDownwardCap.first_source_contact_cases {t x : ℝ}
    (ht : t ∈ regularCornerDomain m)
    (hy : 0 < sweptNiche U (Real.pi / 2) x)
    (hmax : fullWallClip hU.toCompactCap x t = sweptNiche U (Real.pi / 2) x)
    (hfirst : firstWall U t x = sweptNiche U (Real.pi / 2) x) :
    (firstWall U t x < secondWall U t x ∧
      (x, sweptNiche U (Real.pi / 2) x) = firstTangency U t) ∨
      (firstWall U t x = secondWall U t x ∧
        (x, sweptNiche U (Real.pi / 2) x) = attachedCorner U t) := by
  have hcorner := positive_fullWallClip_eq_cornerWall hy hmax
  have hle : firstWall U t x ≤ secondWall U t x := by
    rw [hfirst, ← hcorner]
    exact min_le_right _ _
  rcases hle.eq_or_lt with he | hs
  · exact Or.inr ⟨he, wall_tie_eq_attachedCorner ht.1 hfirst (he.symm.trans hfirst)⟩
  · exact Or.inl ⟨hs, hU.first_strict_contact_eq_tangency hρ hρ0 hρK heq ht hfirst hs⟩

theorem IsDownwardCap.second_source_contact_cases {t x : ℝ}
    (ht : t ∈ regularCornerDomain m)
    (hy : 0 < sweptNiche U (Real.pi / 2) x)
    (hmax : fullWallClip hU.toCompactCap x t = sweptNiche U (Real.pi / 2) x)
    (hsecond : secondWall U t x = sweptNiche U (Real.pi / 2) x) :
    (secondWall U t x < firstWall U t x ∧
      (x, sweptNiche U (Real.pi / 2) x) = secondTangency U t) ∨
      (firstWall U t x = secondWall U t x ∧
        (x, sweptNiche U (Real.pi / 2) x) = attachedCorner U t) := by
  have hcorner := positive_fullWallClip_eq_cornerWall hy hmax
  have hle : secondWall U t x ≤ firstWall U t x := by
    rw [hsecond, ← hcorner]
    exact min_le_left _ _
  rcases hle.eq_or_lt with he | hs
  · exact Or.inr ⟨he.symm, wall_tie_eq_attachedCorner ht.1 (he.symm.trans hsecond) hsecond⟩
  · exact Or.inl ⟨hs, hU.second_strict_contact_eq_tangency hρ hρ0 hρK heq ht hsecond hs⟩

/-- At a strict second-wall maximum, a negative derivative of its
tangent abscissa would make the angular wall have positive second
derivative. Thus the literal companion curvature cannot exceed one. -/
theorem IsDownwardCap.companion_density_le_one_at_strict_contact {t x k : ℝ}
    (ht : t ∈ regularCornerDomain m)
    (hcontact : secondWall U t x = sweptNiche U (Real.pi / 2) x)
    (hstrict : secondWall U t x < firstWall U t x)
    (hDx : HasDerivAt (fun s => (secondTangency U s).1) ((1 - k) * Real.cos t) t) :
    k ≤ 1 := by
  have hpoint := hU.second_strict_contact_eq_tangency hρ hρ0 hρK heq ht hcontact hstrict
  have hx : x = (secondTangency U t).1 := congrArg Prod.fst hpoint
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1.1, Real.pi_pos], ht.1.2⟩
  have hd : HasDerivAt (fun s => (x - (secondTangency U s).1) / Real.cos s ^ 2)
      ((k - 1) / Real.cos t) t := by
    apply (((hasDerivAt_const t x).sub hDx).div
      ((Real.hasDerivAt_cos t).pow 2) (pow_ne_zero 2 hc.ne')).congr_deriv
    rw [hx]
    field_simp [hc.ne']
    ring
  have hderiv : (deriv (fun s => secondWall U s x)) =ᶠ[𝓝 t]
      (fun s => (x - (secondTangency U s).1) / Real.cos s ^ 2) := by
    filter_upwards [(isOpen_regularCornerDomain m).mem_nhds ht] with s hs
    exact (hU.hasDerivAt_walls_on_regularCornerDomain hρ hρ0 hρK heq hs x).2.deriv
  have hd₂ := hd.congr_of_eventuallyEq hderiv
  have hmax := hU.secondWall_isLocalMax_of_strict_contact hρ hρ0 hρK heq ht hcontact hstrict
  have hnonpos := second_deriv_nonpos_of_isLocalMax hmax
    (hU.hasDerivAt_walls_on_regularCornerDomain hρ hρ0 hρK heq ht x).2.continuousAt
  rw [hd₂.deriv] at hnonpos
  by_contra hnot
  exact (not_le_of_gt (div_pos (sub_pos.mpr (lt_of_not_ge hnot)) hc)) hnonpos

theorem IsDownwardCap.ae_companion_density_le_one_at_strict_contact :
    ∀ᵐ t ∂volume.restrict (regularCornerDomain m), ∀ x : ℝ,
      secondWall U t x = sweptNiche U (Real.pi / 2) x →
      secondWall U t x < firstWall U t x → ρ (t + Real.pi / 2) ≤ 1 := by
  filter_upwards [ae_restrict_mem (isOpen_regularCornerDomain m).measurableSet,
    hU.ae_hasDerivAt_tangency_coordinates_on_regularCornerDomain hρ hρ0 hρK heq]
    with t ht hd
  intro x hx hstrict
  exact hU.companion_density_le_one_at_strict_contact hρ hρ0 hρK heq ht hx hstrict hd.2.2.1

end ActualDensity

end AmbidextrousSofa
