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
  have hfull := regularCornerDomain_zero.ge
  have hreg := hquarter.trans hfull
  have hdir := regularCornerDomain_interval_directions hreg
  have hD := hU.isCap.secondTangency_monotoneOn_open_of_unit_density
    hρ hρ0 hρC heq hfull hcompanion
  have hB := hU.isCap.firstTangency_monotoneOn_open_of_unit_density
    hρ hρ0 hρC heq (fun u hu => hfull ⟨hb₀.trans_lt hu.1, hu.2⟩) hfuture
  have hwalls (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) (Real.pi / 2)) (x : ℝ) :=
    hU.isCap.hasDerivAt_walls_on_regularCornerDomain hρ hρ0 hρC heq (hfull hu) x
  have hS := fun u hu x => (hwalls u hu x).2
  have hDvisible (u : ℝ) (hu : u ∈ Icc s t) :=
    sweptNiche_at_secondTangency hU.isCap hD.1 hS (hquarter hu) (hq u hu).le (hDy u hu)
  have hcvisible (u : ℝ) (hu : u ∈ Icc s t) :=
    sweptNiche_at_visible_corner hU.isCap hb₀ hD.1 hB.1 (fun u hu x => (hwalls u hu x).1) hS
      (hsub hu) (hq u hu) (hr u hu) (hcy u hu)
  have hsI : s ∈ Icc s t := left_mem_Icc.mpr hst.le
  have htI : t ∈ Icc s t := right_mem_Icc.mpr hst.le
  -- On both open graph pieces the niche is positive and every maximizing angle lies in `(s, t)`.
  have hpiece : ∀ x ∈ Ioo (secondTangency U s).1 (secondTangency U t).1 ∪
      Ioo (attachedCorner U t).1 (attachedCorner U s).1, 0 < sweptNiche U (Real.pi / 2) x ∧
        (∀ v ∈ Icc (0 : ℝ) (Real.pi / 2),
          fullWallClip hU.isCap.toCompactCap x v = sweptNiche U (Real.pi / 2) x → v ∈ Ioo s t) := by
    rintro x (hx | hx)
    · obtain ⟨u, hu, rfl⟩ := intermediate_value_Icc hst.le
        ((hU.isCap.continuousOn_tangency_coordinates_on_regularCornerDomain
          hρ hρ0 hρC heq).2.2.1.mono hreg) (Ioo_subset_Icc_self hx)
      have hsu : Icc s u ⊆ Icc s t := Icc_subset_Icc le_rfl hu.2
      have hpos : 0 < (secondTangency U u).2 :=
        hU.isCap.secondTangency_snd_pos_of_fst_gt hρ hρ0 hρC heq hu.1 (hsu.trans hquarter)
          (hsu.trans hdir.1) ((Icc_subset_Icc le_rfl (by linarith [hu.2])).trans hdir.2)
          (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Icc_self.trans (hsu.trans hquarter))
            hcompanion) (hDy s hsI) hx.1
      refine ⟨hpos.trans_eq (hDvisible u hu).symm, fun v hv hmax => ?_⟩
      obtain ⟨hvq, hvx⟩ := secondTangency_abscissa_of_maximizing_angle hU.isCap hD.1 hS
        (hquarter hu) (hq u hu).le hpos hv hmax
      exact ⟨lt_of_not_ge fun h => hx.1.not_ge (hvx.symm.trans_le (hD.1 hvq (hquarter hsI) h)),
        lt_of_not_ge fun h => hx.2.not_ge ((hD.1 (hquarter htI) hvq h).trans_eq hvx)⟩
    · obtain ⟨u, hu, rfl⟩ := intermediate_value_Icc' hst.le
        (continuous_attachedCorner hU.isCap.isCompact).fst.continuousOn (Ioo_subset_Icc_self hx)
      refine ⟨(hcy u hu).trans_eq (hcvisible u hu).1.symm, fun v hv hmax => ?_⟩
      rw [(hcvisible u hu).2 v hv hmax]
      exact ⟨hu.1.lt_of_ne (by rintro rfl; exact hx.2.false),
        hu.2.lt_of_ne (by rintro rfl; exact hx.1.false)⟩
  have hbound := hU.nicheGraphProjection_add_le_curvature_of_open_pieces hheight (m := 0) (c := c)
    (by simpa only [zero_mul, zero_add] using haffine) (by linarith only [hst]) hdir.2 hst.le hdir.1
    (sub_nonneg.2 hst.le) (fun _ j hj => (AngularGrid.localized_quarter_source _ hθ j hj).1) hleft
    (hD.1 (hquarter hsI) (hquarter htI) hst.le)
    (sub_le_self _ (mul_pos (hq t htI) (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [(hquarter htI).1, Real.pi_pos], (hquarter htI).2⟩)).le)
    (hU.isCap.attachedCorner_fst_strictAntiOn_of_opposite_velocities hρ hρ0 hρC heq hreg
      (fun u hu => hq u (Ioo_subset_Icc_self hu)) (fun u hu => hr u (Ioo_subset_Icc_self hu))
      hsI htI hst).le hright (fun x hx => (hpiece x hx).1) (fun x hx => (hpiece x hx).2)
  simpa only [nicheGraphProjection, hDvisible s hsI, hDvisible t htI,
    (hcvisible s hsI).1, (hcvisible t htI).1] using hbound

end AmbidextrousSofa
