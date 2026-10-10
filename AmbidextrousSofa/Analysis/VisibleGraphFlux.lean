module

public import AmbidextrousSofa.Analysis.OpenGraphFlux
public import AmbidextrousSofa.Analysis.RegularCorner
public import AmbidextrousSofa.Analysis.TangencyOrder

@[expose] public section

/-!
# Actual visible tangency and corner flux

A unit companion quarter makes the second tangency abscissa monotone.
A unit future of the first quarter makes the opposite-sign corner
strictly visible. Interior points of the tangency graph localize every
maximizing angle even when the tangency has plateaus. The two actual
graph pieces are disjoint and their projected increments are bounded
by the literal companion curvature, with a local quadratic error.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem IsFullCapMaximizer.visible_tangency_corner_flux
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C c b₀ s t θ : ℝ}
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = c)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hb₀ : 0 ≤ b₀)
    (hcompanion : ∀ᵐ u ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ (u + Real.pi / 2) ≤ 1)
    (hfuture : ∀ᵐ u ∂volume.restrict (Ioo b₀ (Real.pi / 2)), ρ u ≤ 1)
    (hst : s < t) (hθ : θ ∈ Icc s t)
    (hsub : Icc s t ⊆ Ioo b₀ (Real.pi / 2))
    (hq : ∀ u ∈ Icc s t, 0 < firstCornerVelocity U u)
    (hr : ∀ u ∈ Icc s t, 0 < secondCornerVelocity U u)
    (hDy : ∀ u ∈ Icc s t, 0 ≤ (secondTangency U u).2)
    (hcy : ∀ u ∈ Icc s t, 0 < (attachedCorner U u).2)
    (hleft : horizontalLeft U + capWidth U / 4 ≤ (secondTangency U s).1)
    (hright : (attachedCorner U s).1 ≤ horizontalRight U - capWidth U / 4) :
    Real.cos θ * ((secondTangency U t).1 - (secondTangency U s).1) +
      Real.sin θ * ((secondTangency U t).2 - (secondTangency U s).2) +
      (Real.cos θ * ((attachedCorner U s).1 - (attachedCorner U t).1) +
        Real.sin θ * ((attachedCorner U s).2 - (attachedCorner U t).2)) ≤
      (upperCurvature U).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2)) +
        (t - s) * ((upperCurvature U).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2)) +
          (upperCurvature U).real (Ioc s t)) := by
  have hquarter : Icc s t ⊆ Ioo (0 : ℝ) (Real.pi / 2) :=
    fun u hu => ⟨hb₀.trans_lt (hsub hu).1, (hsub hu).2⟩
  have hfull : Ioo (0 : ℝ) (Real.pi / 2) ⊆ regularCornerDomain 0 := by
    intro u hu
    simpa only [regularCornerDomain_zero] using hu
  have hreg : Icc s t ⊆ regularCornerDomain 0 := hquarter.trans hfull
  have hdir := regularCornerDomain_interval_directions hreg
  have hD := hU.isCap.secondTangency_monotoneOn_open_of_unit_density
    hρ hρ0 hρC heq hfull hcompanion
  have hfutureReg : Ioo b₀ (Real.pi / 2) ⊆ regularCornerDomain 0 :=
    fun u hu => hfull ⟨hb₀.trans_lt hu.1, hu.2⟩
  have hB := hU.isCap.firstTangency_monotoneOn_open_of_unit_density
    hρ hρ0 hρC heq hfutureReg hfuture
  have hwalls := fun (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) (Real.pi / 2)) (x : ℝ) =>
    hU.isCap.hasDerivAt_walls_on_regularCornerDomain hρ hρ0 hρC heq (hfull hu) x
  have hS := fun u hu x => (hwalls u hu x).2
  have hR := fun u hu x => (hwalls u hu x).1
  have hDcont : ContinuousOn (fun u => (secondTangency U u).1) (Icc s t) :=
    (hU.isCap.continuousOn_tangency_coordinates_on_regularCornerDomain
      hρ hρ0 hρC heq).2.2.1.mono hreg
  have hccont : ContinuousOn (fun u => (attachedCorner U u).1) (Icc s t) :=
    (continuous_attachedCorner hU.isCap.isCompact).fst.continuousOn
  have hcanti := hU.isCap.attachedCorner_fst_strictAntiOn_of_opposite_velocities
    hρ hρ0 hρC heq hreg
    (fun u hu => hq u (Ioo_subset_Icc_self hu))
    (fun u hu => hr u (Ioo_subset_Icc_self hu))
  have hDvisible (u : ℝ) (hu : u ∈ Icc s t) :
      sweptNiche U (Real.pi / 2) (secondTangency U u).1 = (secondTangency U u).2 :=
    sweptNiche_at_secondTangency hU.isCap hD.1 hS (hquarter hu) (hq u hu).le (hDy u hu)
  have hcvisible (u : ℝ) (hu : u ∈ Icc s t) :
      sweptNiche U (Real.pi / 2) (attachedCorner U u).1 = (attachedCorner U u).2 ∧
        (∀ v ∈ Icc (0 : ℝ) (Real.pi / 2),
          fullWallClip hU.isCap.toCompactCap (attachedCorner U u).1 v =
            sweptNiche U (Real.pi / 2) (attachedCorner U u).1 → v = u) :=
    sweptNiche_at_visible_corner hU.isCap hb₀ hD.1 hB.1 hR hS
      (hsub hu) (hq u hu) (hr u hu) (hcy u hu)
  have hDpiece : ∀ x ∈ Ioo (secondTangency U s).1 (secondTangency U t).1,
      0 < sweptNiche U (Real.pi / 2) x ∧
        (∀ v ∈ Icc (0 : ℝ) (Real.pi / 2),
          fullWallClip hU.isCap.toCompactCap x v = sweptNiche U (Real.pi / 2) x → v ∈ Ioo s t) := by
    intro x hx
    obtain ⟨u, hu, hux⟩ := intermediate_value_Icc hst.le hDcont (Ioo_subset_Icc_self hx)
    have hsuReg : Icc s u ⊆ regularCornerDomain 0 :=
      fun v hv => hreg ⟨hv.1, hv.2.trans hu.2⟩
    have hsuDirections := regularCornerDomain_interval_directions hsuReg
    have hunit : ∀ᵐ v ∂volume.restrict (Ioo s u), ρ (v + Real.pi / 2) ≤ 1 :=
      ae_restrict_of_ae_restrict_of_subset
        (fun v hv => hquarter ⟨hv.1.le, hv.2.le.trans hu.2⟩) hcompanion
    have hDypos : 0 < (secondTangency U u).2 :=
      hU.isCap.secondTangency_snd_pos_of_fst_gt hρ hρ0 hρC heq hu.1
        (fun v hv => hquarter ⟨hv.1, hv.2.trans hu.2⟩)
        hsuDirections.1 hsuDirections.2 hunit (hDy s (left_mem_Icc.mpr hst.le))
        (by simpa only [hux] using hx.1)
    have hNx : sweptNiche U (Real.pi / 2) x = (secondTangency U u).2 := by
      rw [← hux]
      exact hDvisible u hu
    refine ⟨by rw [hNx]; exact hDypos, ?_⟩
    intro v hv hmax
    have hmax' : fullWallClip hU.isCap.toCompactCap (secondTangency U u).1 v =
        sweptNiche U (Real.pi / 2) (secondTangency U u).1 := by
      simpa only [hux] using hmax
    have hvD := secondTangency_abscissa_of_maximizing_angle hU.isCap hD.1 hS
      (hquarter hu) (hq u hu).le hDypos hv hmax'
    have hvx : (secondTangency U v).1 = x := hvD.2.trans hux
    constructor
    · by_contra hnot
      have hle : (secondTangency U v).1 ≤ (secondTangency U s).1 :=
        hD.1 hvD.1 (hquarter (left_mem_Icc.mpr hst.le)) (le_of_not_gt hnot)
      rw [hvx] at hle
      exact (not_le_of_gt hx.1) hle
    · by_contra hnot
      have hle : (secondTangency U t).1 ≤ (secondTangency U v).1 :=
        hD.1 (hquarter (right_mem_Icc.mpr hst.le)) hvD.1 (le_of_not_gt hnot)
      rw [hvx] at hle
      exact (not_le_of_gt hx.2) hle
  have hcpiece : ∀ x ∈ Ioo (attachedCorner U t).1 (attachedCorner U s).1,
      0 < sweptNiche U (Real.pi / 2) x ∧
        (∀ v ∈ Icc (0 : ℝ) (Real.pi / 2),
          fullWallClip hU.isCap.toCompactCap x v = sweptNiche U (Real.pi / 2) x → v ∈ Ioo s t) := by
    intro x hx
    obtain ⟨u, hu, hux⟩ := intermediate_value_Icc' hst.le hccont (Ioo_subset_Icc_self hx)
    have hNx : sweptNiche U (Real.pi / 2) x = (attachedCorner U u).2 := by
      rw [← hux]
      exact (hcvisible u hu).1
    refine ⟨by rw [hNx]; exact hcy u hu, ?_⟩
    intro v hv hmax
    have hmax' : fullWallClip hU.isCap.toCompactCap (attachedCorner U u).1 v =
        sweptNiche U (Real.pi / 2) (attachedCorner U u).1 := by simpa only [hux] using hmax
    have hvu : v = u := (hcvisible u hu).2 v hv hmax'
    rw [hvu]
    constructor
    · apply lt_of_le_of_ne hu.1
      intro heq
      have hux' : (attachedCorner U s).1 = x := by simpa only [← heq] using hux
      exact (ne_of_lt hx.2) hux'.symm
    · apply lt_of_le_of_ne hu.2
      intro heq
      have hux' : (attachedCorner U t).1 = x := by simpa only [heq] using hux
      exact (ne_of_lt hx.1) hux'
  have hsI : s ∈ Icc s t := left_mem_Icc.mpr hst.le
  have htI : t ∈ Icc s t := right_mem_Icc.mpr hst.le
  have hDorder := hD.1 (hquarter hsI) (hquarter htI) hst.le
  have hcorder := hcanti hsI htI hst
  have hgap : (secondTangency U t).1 ≤ (attachedCorner U t).1 := by
    have hcos : 0 < Real.cos t :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [(hquarter htI).1, Real.pi_pos], (hquarter htI).2⟩
    dsimp only [secondTangency]
    nlinarith [mul_pos (hq t htI) hcos]
  have hbound := hU.nicheGraphProjection_add_le_curvature_of_open_pieces hheight
    (m := 0) (c := c) (by simpa only [zero_mul, zero_add] using haffine)
    hθ hdir.1 hdir.2 hleft hDorder hgap hcorder hright
    (fun x hx => by
      rcases hx with hx | hx
      · exact (hDpiece x hx).1
      · exact (hcpiece x hx).1)
    (fun x hx v hv hmax => by
      rcases hx with hx | hx
      · exact (hDpiece x hx).2 v hv hmax
      · exact (hcpiece x hx).2 v hv hmax)
  simpa only [nicheGraphProjection, hDvisible s hsI, hDvisible t htI,
    (hcvisible s hsI).1, (hcvisible t htI).1] using hbound

end AmbidextrousSofa
