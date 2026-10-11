module

public import AmbidextrousSofa.Analysis.TangencyLoci

@[expose] public section

/-!
# Tangency calculus on actual open regular intervals

The density representation excludes only the stated actual exceptional
normals. Every regular corner angle lies inside a closed interval with
two regular directions, so compact interval calculus applies locally
throughout the regular corner domain, and unit density gives monotonicity
on any open interval contained in that domain. No endpoint atom is crossed.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem regularCornerDomain_interval_directions {m a b : ℝ}
    (hsub : Icc a b ⊆ regularCornerDomain m) :
    Icc a b ⊆ regularCurvatureDomain m ∧
      Icc (a + Real.pi / 2) (b + Real.pi / 2) ⊆ regularCurvatureDomain m := by
  refine ⟨fun t ht => (hsub ht).2.1, fun t ht => ?_⟩
  simpa only [mem_preimage, sub_add_cancel] using (hsub (⟨by linarith [ht.1], by linarith [ht.2]⟩ :
    t - Real.pi / 2 ∈ Icc a b)).2.2

/-- Every regular corner angle is interior to a closed interval with two regular directions. -/
theorem exists_regularCornerDomain_interval {m t : ℝ} (ht : t ∈ regularCornerDomain m) :
    ∃ a b : ℝ, t ∈ Ioo a b ∧ a ≤ b ∧ Icc a b ⊆ regularCurvatureDomain m ∧
      Icc (a + Real.pi / 2) (b + Real.pi / 2) ⊆ regularCurvatureDomain m := by
  obtain ⟨l, r, htI, hI⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp ((isOpen_regularCornerDomain m).mem_nhds ht)
  exact ⟨(l + t) / 2, (t + r) / 2, ⟨by linarith [htI.1], by linarith [htI.2]⟩,
    by linarith [htI.1, htI.2], regularCornerDomain_interval_directions fun x hx =>
      hI ⟨by linarith [hx.1, htI.1], by linarith [hx.2, htI.2]⟩⟩

variable {U : Set Plane} (hU : IsDownwardCap U) {ρ : ℝ → ℝ} {C m a b t : ℝ}
  (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun x => ENNReal.ofReal (ρ x)))
include hU hρ hρ0 hρC heq

theorem IsDownwardCap.hasDerivAt_walls_on_regularCornerDomain
    (ht : t ∈ regularCornerDomain m) (x : ℝ) :
    HasDerivAt (fun s => firstWall U s x)
        ((x - (firstTangency U t).1) / Real.sin t ^ 2) t ∧
      HasDerivAt (fun s => secondWall U s x)
        ((x - (secondTangency U t).1) / Real.cos t ^ 2) t := by
  obtain ⟨a, b, htI, -, hbase, hshift⟩ := exists_regularCornerDomain_interval ht
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ht.1
  exact ⟨hU.hasDerivAt_firstWall_angle_of_density hρ hρ0 hρC heq hbase htI hs.ne' x,
    hU.hasDerivAt_secondWall_angle_of_density hρ hρ0 hρC heq hshift htI hc.ne' x⟩

theorem IsDownwardCap.continuousOn_tangency_coordinates_on_regularCornerDomain :
    ContinuousOn (fun t => (firstTangency U t).1) (regularCornerDomain m) ∧
      ContinuousOn (fun t => (firstTangency U t).2) (regularCornerDomain m) ∧
      ContinuousOn (fun t => (secondTangency U t).1) (regularCornerDomain m) ∧
      ContinuousOn (fun t => (secondTangency U t).2) (regularCornerDomain m) := by
  simp only [(isOpen_regularCornerDomain m).continuousOn_iff, ← forall₂_and]
  intro t ht
  obtain ⟨a, b, htI, hab, hbase, hshift⟩ := exists_regularCornerDomain_interval ht
  have hac := hU.absolutelyContinuousOnInterval_tangency_coordinates_of_density
    hρ hρ0 hρC heq hab hbase hshift
  have hnbhd : uIcc a b ∈ 𝓝 t := mem_of_superset (Icc_mem_nhds htI.1 htI.2) Icc_subset_uIcc
  exact ⟨hac.1.continuousOn.continuousAt hnbhd, hac.2.1.continuousOn.continuousAt hnbhd,
    hac.2.2.1.continuousOn.continuousAt hnbhd, hac.2.2.2.continuousOn.continuousAt hnbhd⟩

theorem IsDownwardCap.firstTangency_monotoneOn_open_of_unit_density
    (hsub : Ioo a b ⊆ regularCornerDomain m)
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo a b), ρ t ≤ 1) :
    MonotoneOn (fun t => (firstTangency U t).1) (Ioo a b) ∧
      AntitoneOn (fun t => (firstTangency U t).2) (Ioo a b) := by
  have h {x y} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) (hxy : x ≤ y) :=
    have hclosed : Icc x y ⊆ regularCornerDomain m := fun t ht =>
      hsub ⟨hx.1.trans_le ht.1, ht.2.trans_lt hy.2⟩
    (hU.tangency_monotone_of_unit_density hρ hρ0 hρC heq hxy (fun t ht => (hclosed ht).1)
      (regularCornerDomain_interval_directions hclosed).1
      (regularCornerDomain_interval_directions hclosed).2).1
      (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hx.1.le hy.2.le) hunit)
  exact ⟨fun _ hx _ hy hxy => (h hx hy hxy).1 (left_mem_Icc.2 hxy) (right_mem_Icc.2 hxy) hxy,
    fun _ hx _ hy hxy => (h hx hy hxy).2 (left_mem_Icc.2 hxy) (right_mem_Icc.2 hxy) hxy⟩

theorem IsDownwardCap.secondTangency_monotoneOn_open_of_unit_density
    (hsub : Ioo a b ⊆ regularCornerDomain m)
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo a b), ρ (t + Real.pi / 2) ≤ 1) :
    MonotoneOn (fun t => (secondTangency U t).1) (Ioo a b) ∧
      MonotoneOn (fun t => (secondTangency U t).2) (Ioo a b) := by
  have h {x y} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) (hxy : x ≤ y) :=
    have hclosed : Icc x y ⊆ regularCornerDomain m := fun t ht =>
      hsub ⟨hx.1.trans_le ht.1, ht.2.trans_lt hy.2⟩
    (hU.tangency_monotone_of_unit_density hρ hρ0 hρC heq hxy (fun t ht => (hclosed ht).1)
      (regularCornerDomain_interval_directions hclosed).1
      (regularCornerDomain_interval_directions hclosed).2).2
      (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hx.1.le hy.2.le) hunit)
  exact ⟨fun _ hx _ hy hxy => (h hx hy hxy).1 (left_mem_Icc.2 hxy) (right_mem_Icc.2 hxy) hxy,
    fun _ hx _ hy hxy => (h hx hy hxy).2 (left_mem_Icc.2 hxy) (right_mem_Icc.2 hxy) hxy⟩

end AmbidextrousSofa
