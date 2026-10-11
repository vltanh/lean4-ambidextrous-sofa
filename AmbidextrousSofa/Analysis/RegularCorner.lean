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
  rw [ae_iff, Measure.restrict_apply' hS.measurableSet]
  refine measure_null_of_locally_null _ fun x hx => ?_
  obtain ⟨a, b, hxI, hI⟩ := hlocal x hx.2
  rw [ae_iff, Measure.restrict_apply' measurableSet_Ioo] at hI
  exact ⟨_, inter_mem_nhdsWithin _ (Ioo_mem_nhds hxI.1 hxI.2),
    measure_mono_null (inter_subset_inter_left _ inter_subset_left) hI⟩

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
  have hdir := regularCornerDomain_interval_directions hsub
  have hac := hU.absolutelyContinuousOnInterval_cornerVelocities_of_density
    hρ hρ0 hρC heq (htI.1.le.trans htI.2.le) hdir.1 hdir.2
  have hnbhd : uIcc a b ∈ 𝓝 t := mem_of_superset (Icc_mem_nhds htI.1 htI.2) Icc_subset_uIcc
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
  refine ae_restrict_of_local_intervals (isOpen_regularCornerDomain m) fun t ht => ?_
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
  have hderiv (t) (ht : t ∈ Icc a b) :=
    (hU.hasDerivAt_corner_coordinates_on_regularCornerDomain hρ hρ0 hρC heq (hsub ht)).1
  refine strictAntiOn_of_deriv_neg (convex_Icc a b)
    (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt) fun t ht => ?_
  rw [interior_Icc] at ht
  obtain ⟨h0, h1⟩ := (hsub (Ioo_subset_Icc_self ht)).1
  rw [(hderiv t (Ioo_subset_Icc_self ht)).deriv, cornerVelocityX]
  linarith [mul_pos (hq t ht) (Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])),
    mul_pos (hr t ht) (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩)]

end AmbidextrousSofa
