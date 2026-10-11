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
  by_contra! hpos
  have hmin := isLocalMin_of_deriv_deriv_pos hpos hmax.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 t] fun _ => f t := (hmax.and hmin).mono fun _ h => le_antisymm h.1 h.2
  simp only [heq.deriv.deriv_eq, deriv_const', deriv_const, lt_self_iff_false] at hpos

theorem positive_fullWallClip_eq_cornerWall {U : CompactCap} {t x : ℝ}
    (hy : 0 < sweptNiche U (Real.pi / 2) x)
    (hmax : fullWallClip U x t = sweptNiche U (Real.pi / 2) x) :
    cornerWall U t x = sweptNiche U (Real.pi / 2) x := by
  rw [← hmax] at hy ⊢
  exact (max_eq_left (lt_max_iff.mp hy |>.resolve_right (lt_irrefl 0)).le).symm

theorem wall_tie_eq_attachedCorner {U : Set Plane} {t x y : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hfirst : firstWall U t x = y) (hsecond : secondWall U t x = y) :
    (x, y) = attachedCorner U t := by
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ht
  have hw := hfirst.trans hsecond.symm
  obtain rfl : x = (attachedCorner U t).1 := le_antisymm
    ((secondWall_le_firstWall_iff hs hc).mp hw.ge) ((firstWall_le_secondWall_iff hs hc).mp hw.le)
  exact Prod.ext rfl (hfirst.symm.trans (firstWall_attachedCorner U hs.ne'))

section ActualDensity

variable {U : Set Plane} (hU : IsDownwardCap U) {m K : ℝ} {ρ : ℝ → ℝ}
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

include hU hρ hρ0 hρK heq in
theorem IsDownwardCap.first_strict_contact_eq_tangency {t x : ℝ}
    (ht : t ∈ regularCornerDomain m)
    (hcontact : firstWall U t x = sweptNiche U (Real.pi / 2) x)
    (hstrict : firstWall U t x < secondWall U t x) :
    (x, sweptNiche U (Real.pi / 2) x) = firstTangency U t := by
  have hd := hU.hasDerivAt_walls_on_regularCornerDomain hρ hρ0 hρK heq ht x
  have hmax : IsLocalMax (fun s => firstWall U s x) t := by
    filter_upwards [hd.1.continuousAt.eventually_lt hd.2.continuousAt hstrict,
      Ioo_mem_nhds ht.1.1 ht.1.2] with s hs hsI
    rw [hcontact, ← min_eq_left hs.le]
    exact cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCompact le_rfl x) hsI
  have hs : Real.sin t ≠ 0 :=
    (sin_cos_pos_of_mem_quarter ht.1).1.ne'
  obtain rfl : x = (firstTangency U t).1 :=
    sub_eq_zero.mp ((div_eq_zero_iff.mp (hmax.hasDerivAt_eq_zero hd.1)).resolve_right
      (pow_ne_zero 2 hs))
  exact Prod.ext rfl (hcontact.symm.trans (firstWall_firstTangency U hs))

include hU hρ hρ0 hρK heq in
theorem IsDownwardCap.secondWall_isLocalMax_of_strict_contact {t x : ℝ}
    (ht : t ∈ regularCornerDomain m)
    (hcontact : secondWall U t x = sweptNiche U (Real.pi / 2) x)
    (hstrict : secondWall U t x < firstWall U t x) :
    IsLocalMax (fun s => secondWall U s x) t := by
  have hd := hU.hasDerivAt_walls_on_regularCornerDomain hρ hρ0 hρK heq ht x
  filter_upwards [hd.2.continuousAt.eventually_lt hd.1.continuousAt hstrict,
    Ioo_mem_nhds ht.1.1 ht.1.2] with s hs hsI
  rw [hcontact, ← min_eq_right hs.le]
  exact cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCompact le_rfl x) hsI

include hU hρ hρ0 hρK heq in
theorem IsDownwardCap.second_strict_contact_eq_tangency {t x : ℝ}
    (ht : t ∈ regularCornerDomain m)
    (hcontact : secondWall U t x = sweptNiche U (Real.pi / 2) x)
    (hstrict : secondWall U t x < firstWall U t x) :
    (x, sweptNiche U (Real.pi / 2) x) = secondTangency U t := by
  have hc : Real.cos t ≠ 0 :=
    (sin_cos_pos_of_mem_quarter ht.1).2.ne'
  have hz := (hU.secondWall_isLocalMax_of_strict_contact hρ hρ0 hρK heq ht hcontact
    hstrict).hasDerivAt_eq_zero (hU.hasDerivAt_walls_on_regularCornerDomain hρ hρ0 hρK heq ht x).2
  obtain rfl : x = (secondTangency U t).1 :=
    sub_eq_zero.mp ((div_eq_zero_iff.mp hz).resolve_right (pow_ne_zero 2 hc))
  exact Prod.ext rfl (hcontact.symm.trans (secondWall_secondTangency U hc))

include hU hρ hρ0 hρK heq in
/-- At a strict second-wall maximum, a negative derivative of its
tangent abscissa would make the angular wall have positive second
derivative. Thus the literal companion curvature cannot exceed one. -/
theorem IsDownwardCap.ae_companion_density_le_one_at_strict_contact :
    ∀ᵐ t ∂volume.restrict (regularCornerDomain m), ∀ x : ℝ,
      secondWall U t x = sweptNiche U (Real.pi / 2) x →
      secondWall U t x < firstWall U t x → ρ (t + Real.pi / 2) ≤ 1 := by
  filter_upwards [ae_restrict_mem (isOpen_regularCornerDomain m).measurableSet,
    hU.ae_hasDerivAt_tangency_coordinates_on_regularCornerDomain hρ hρ0 hρK heq]
    with t ht hDx x hcontact hstrict
  have hx : x = (secondTangency U t).1 :=
    congrArg Prod.fst (hU.second_strict_contact_eq_tangency hρ hρ0 hρK heq ht hcontact hstrict)
  have hc : 0 < Real.cos t := (sin_cos_pos_of_mem_quarter ht.1).2
  have hd : HasDerivAt (fun s => (x - (secondTangency U s).1) / Real.cos s ^ 2)
      ((ρ (t + Real.pi / 2) - 1) / Real.cos t) t := by
    refine (((hasDerivAt_const t x).sub hDx.2.2.1).div ((Real.hasDerivAt_cos t).pow 2)
      (pow_ne_zero 2 hc.ne')).congr_deriv ?_
    simp only [Pi.sub_apply, Pi.pow_apply, hx, sub_self]
    field_simp
    ring
  have hderiv : deriv (fun s => secondWall U s x) =ᶠ[𝓝 t]
      fun s => (x - (secondTangency U s).1) / Real.cos s ^ 2 := by
    filter_upwards [(isOpen_regularCornerDomain m).mem_nhds ht] with s hs
    exact (hU.hasDerivAt_walls_on_regularCornerDomain hρ hρ0 hρK heq hs x).2.deriv
  have hnonpos := second_deriv_nonpos_of_isLocalMax
    (hU.secondWall_isLocalMax_of_strict_contact hρ hρ0 hρK heq ht hcontact hstrict)
    (hU.hasDerivAt_walls_on_regularCornerDomain hρ hρ0 hρK heq ht x).2.continuousAt
  rw [(hd.congr_of_eventuallyEq hderiv).deriv] at hnonpos
  by_contra! hk
  exact hnonpos.not_gt (div_pos (sub_pos.mpr hk) hc)

end ActualDensity

end AmbidextrousSofa
