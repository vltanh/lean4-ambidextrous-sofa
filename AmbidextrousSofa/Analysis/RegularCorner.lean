module

public import AmbidextrousSofa.Analysis.RegularTangency

@[expose] public section

/-!
# Corner calculus on the entire actual regular domain

Local support-density primitives give ordinary corner derivatives and
continuous corner velocities at each regular angle. The a.e. tangency
equations are assembled from genuine local intervals; exceptional
support atoms are never crossed in this assembly.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem ae_restrict_of_local_intervals {S : Set ℝ} {P : ℝ → Prop}
    (hS : IsOpen S)
    (hlocal : ∀ x ∈ S, ∃ a b : ℝ, x ∈ Ioo a b ∧ ∀ᵐ t ∂volume.restrict (Ioo a b), P t) :
    ∀ᵐ x ∂volume.restrict S, P x := by
  let B : Set ℝ := {x ∈ S | ¬ P x}
  have hzero : volume B = 0 := by
    apply measure_null_of_locally_null B
    intro x hx
    obtain ⟨a, b, hxI, hI⟩ := hlocal x hx.1
    have hI' : ∀ᵐ t : ℝ ∂volume, t ∈ Ioo a b → P t :=
      (ae_restrict_iff' measurableSet_Ioo).mp hI
    refine ⟨Ioo a b ∩ B, inter_mem
      (nhdsWithin_le_nhds (Ioo_mem_nhds hxI.1 hxI.2)) self_mem_nhdsWithin, ?_⟩
    apply measure_mono_null _ (ae_iff.mp hI')
    intro t ht hp
    exact ht.2.2 (hp ht.1)
  have hnot : ∀ᵐ x : ℝ ∂volume, x ∉ B := measure_eq_zero_iff_ae_notMem.mp hzero
  apply (ae_restrict_iff' hS.measurableSet).mpr
  filter_upwards [hnot] with x hx hxS
  by_contra hfail
  exact hx ⟨hxS, hfail⟩

theorem IsDownwardCap.hasDerivAt_corner_coordinates_on_regularCornerDomain
    {U : Set Plane} (hU : IsDownwardCap U) {ρ : ℝ → ℝ} {C m t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (ht : t ∈ regularCornerDomain m) :
    HasDerivAt (fun s => (attachedCorner U s).1) (cornerVelocityX U t) t ∧
      HasDerivAt (fun s => (attachedCorner U s).2) (cornerVelocityY U t) t := by
  obtain ⟨a, b, htI, hsub⟩ := exists_closed_interval_within_open
    (isOpen_regularCornerDomain m) ht
  have hdir := regularCornerDomain_interval_directions hsub
  exact ⟨hU.hasDerivAt_attachedCorner_fst_of_density hρ hρ0 hρC heq hdir.1 hdir.2 htI,
    hU.hasDerivAt_attachedCorner_snd_of_density hρ hρ0 hρC heq hdir.1 hdir.2 htI⟩

theorem IsDownwardCap.continuousAt_cornerVelocities_on_regularCornerDomain
    {U : Set Plane} (hU : IsDownwardCap U) {ρ : ℝ → ℝ} {C m t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (ht : t ∈ regularCornerDomain m) :
    ContinuousAt (firstCornerVelocity U) t ∧ ContinuousAt (secondCornerVelocity U) t := by
  obtain ⟨a, b, htI, hsub⟩ := exists_closed_interval_within_open
    (isOpen_regularCornerDomain m) ht
  have hab : a ≤ b := htI.1.le.trans htI.2.le
  have hdir := regularCornerDomain_interval_directions hsub
  have hac := hU.absolutelyContinuousOnInterval_cornerVelocities_of_density
    hρ hρ0 hρC heq hab hdir.1 hdir.2
  have hnbhd : uIcc a b ∈ 𝓝 t := by
    rw [uIcc_of_le hab]
    exact Icc_mem_nhds htI.1 htI.2
  exact ⟨hac.1.continuousOn.continuousAt hnbhd, hac.2.continuousOn.continuousAt hnbhd⟩

theorem IsDownwardCap.ae_hasDerivAt_tangency_coordinates_on_regularCornerDomain
    {U : Set Plane} (hU : IsDownwardCap U) {ρ : ℝ → ℝ} {C m : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun x => ENNReal.ofReal (ρ x))) :
    ∀ᵐ t ∂volume.restrict (regularCornerDomain m),
      HasDerivAt (fun x => (firstTangency U x).1) ((1 - ρ t) * Real.sin t) t ∧
      HasDerivAt (fun x => (firstTangency U x).2) ((ρ t - 1) * Real.cos t) t ∧
      HasDerivAt (fun x => (secondTangency U x).1)
        ((1 - ρ (t + Real.pi / 2)) * Real.cos t) t ∧
      HasDerivAt (fun x => (secondTangency U x).2)
        ((1 - ρ (t + Real.pi / 2)) * Real.sin t) t := by
  apply ae_restrict_of_local_intervals (isOpen_regularCornerDomain m)
  intro t ht
  obtain ⟨a, b, htI, hsub⟩ := exists_closed_interval_within_open
    (isOpen_regularCornerDomain m) ht
  have hdir := regularCornerDomain_interval_directions hsub
  exact ⟨a, b, htI, hU.ae_hasDerivAt_tangency_coordinates_of_density hρ hρ0 hρC heq
    (htI.1.le.trans htI.2.le) hdir.1 hdir.2⟩

theorem IsDownwardCap.attachedCorner_fst_strictAntiOn_of_opposite_velocities
    {U : Set Plane} (hU : IsDownwardCap U) {ρ : ℝ → ℝ} {C m a b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hsub : Icc a b ⊆ regularCornerDomain m)
    (hq : ∀ t ∈ Ioo a b, 0 < firstCornerVelocity U t)
    (hr : ∀ t ∈ Ioo a b, 0 < secondCornerVelocity U t) :
    StrictAntiOn (fun t => (attachedCorner U t).1) (Icc a b) := by
  intro x hx y hy hxy
  have hderiv : ∀ t ∈ Icc x y,
      HasDerivAt (fun s => (attachedCorner U s).1) (cornerVelocityX U t) t := by
    intro t ht
    exact (hU.hasDerivAt_corner_coordinates_on_regularCornerDomain hρ hρ0 hρC heq
      (hsub ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩)).1
  have hmono : StrictMonoOn (fun t => -(attachedCorner U t).1) (Icc x y) :=
    strictMonoOn_of_deriv_pos convex_Icc
      (fun t ht => (hderiv t ht).neg.continuousAt.continuousWithinAt)
      (fun t ht => by
        have htI : t ∈ Ioo x y := by simpa only [interior_Icc] using ht
        have htbig : t ∈ Ioo a b := ⟨hx.1.trans_lt htI.1, htI.2.trans_le hy.2⟩
        have htq := (hsub (Ioo_subset_Icc_self htbig)).1
        have hs := Real.sin_pos_of_pos_of_lt_pi htq.1 (by linarith [htq.2, Real.pi_pos])
        have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [htq.1, Real.pi_pos], htq.2⟩
        rw [(hderiv t (interior_subset ht)).neg.deriv]
        dsimp only [cornerVelocityX]
        nlinarith [mul_pos (hq t htbig) hs, mul_pos (hr t htbig) hc])
  have h := hmono (left_mem_Icc.mpr hxy.le) (right_mem_Icc.mpr hxy.le) hxy
  linarith

end AmbidextrousSofa
