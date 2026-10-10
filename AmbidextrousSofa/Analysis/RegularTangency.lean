import AmbidextrousSofa.Analysis.TangencyLoci

/-!
# Tangency calculus on actual open regular intervals

The density representation excludes only the stated actual exceptional
normals. Compact interval calculus therefore applies locally throughout
the regular corner domain, and unit density gives monotonicity on any
open interval contained in that domain. No endpoint atom is crossed.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem exists_closed_interval_within_open {S : Set ℝ} (hS : IsOpen S)
    {t : ℝ} (ht : t ∈ S) : ∃ a b : ℝ, t ∈ Ioo a b ∧ Icc a b ⊆ S := by
  obtain ⟨l, r, htI, hI⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hS.mem_nhds ht)
  refine ⟨(l + t) / 2, (t + r) / 2, ?_, ?_⟩
  · constructor <;> linarith [htI.1, htI.2]
  · intro x hx
    apply hI
    constructor <;> linarith [hx.1, hx.2, htI.1, htI.2]

theorem regularCornerDomain_interval_directions {m a b : ℝ}
    (hsub : Icc a b ⊆ regularCornerDomain m) :
    Icc a b ⊆ regularCurvatureDomain m ∧
      Icc (a + Real.pi / 2) (b + Real.pi / 2) ⊆ regularCurvatureDomain m := by
  refine ⟨fun t ht => (hsub ht).2.1, ?_⟩
  intro t ht
  have hm : t - Real.pi / 2 ∈ Icc a b := by
    constructor <;> linarith [ht.1, ht.2]
  simpa only [sub_add_cancel] using (hsub hm).2.2

theorem IsDownwardCap.hasDerivAt_walls_on_regularCornerDomain
    {U : Set Plane} (hU : IsDownwardCap U) {ρ : ℝ → ℝ} {C m t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (ht : t ∈ regularCornerDomain m) (x : ℝ) :
    HasDerivAt (fun s => firstWall U s x)
        ((x - (firstTangency U t).1) / Real.sin t ^ 2) t ∧
      HasDerivAt (fun s => secondWall U s x)
        ((x - (secondTangency U t).1) / Real.cos t ^ 2) t := by
  obtain ⟨a, b, htI, hsub⟩ := exists_closed_interval_within_open
    (isOpen_regularCornerDomain m) ht
  have hdirections := regularCornerDomain_interval_directions hsub
  have hs : Real.sin t ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi ht.1.1 (by linarith [ht.1.2, Real.pi_pos])).ne'
  have hc : Real.cos t ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1.1, Real.pi_pos], ht.1.2⟩).ne'
  exact ⟨hU.hasDerivAt_firstWall_angle_of_density hρ hρ0 hρC heq hdirections.1 htI hs x,
    hU.hasDerivAt_secondWall_angle_of_density hρ hρ0 hρC heq hdirections.2 htI hc x⟩

theorem IsDownwardCap.continuousOn_tangency_coordinates_on_regularCornerDomain
    {U : Set Plane} (hU : IsDownwardCap U) {ρ : ℝ → ℝ} {C m : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun x => ENNReal.ofReal (ρ x))) :
    ContinuousOn (fun t => (firstTangency U t).1) (regularCornerDomain m) ∧
      ContinuousOn (fun t => (firstTangency U t).2) (regularCornerDomain m) ∧
      ContinuousOn (fun t => (secondTangency U t).1) (regularCornerDomain m) ∧
      ContinuousOn (fun t => (secondTangency U t).2) (regularCornerDomain m) := by
  have hlocal : ∀ t ∈ regularCornerDomain m,
      ContinuousAt (fun s => (firstTangency U s).1) t ∧
      ContinuousAt (fun s => (firstTangency U s).2) t ∧
      ContinuousAt (fun s => (secondTangency U s).1) t ∧
      ContinuousAt (fun s => (secondTangency U s).2) t := by
    intro t ht
    obtain ⟨a, b, htI, hsub⟩ := exists_closed_interval_within_open
      (isOpen_regularCornerDomain m) ht
    have hab : a ≤ b := htI.1.le.trans htI.2.le
    have hdir := regularCornerDomain_interval_directions hsub
    have hac := hU.absolutelyContinuousOnInterval_tangency_coordinates_of_density
      hρ hρ0 hρC heq hab hdir.1 hdir.2
    have hnbhd : uIcc a b ∈ 𝓝 t := by
      rw [uIcc_of_le hab]
      exact Icc_mem_nhds htI.1 htI.2
    exact ⟨hac.1.continuousOn.continuousAt hnbhd,
      hac.2.1.continuousOn.continuousAt hnbhd,
      hac.2.2.1.continuousOn.continuousAt hnbhd,
      hac.2.2.2.continuousOn.continuousAt hnbhd⟩
  exact ⟨fun t ht => (hlocal t ht).1.continuousWithinAt,
    fun t ht => (hlocal t ht).2.1.continuousWithinAt,
    fun t ht => (hlocal t ht).2.2.1.continuousWithinAt,
    fun t ht => (hlocal t ht).2.2.2.continuousWithinAt⟩

theorem IsDownwardCap.firstTangency_monotoneOn_open_of_unit_density
    {U : Set Plane} (hU : IsDownwardCap U) {ρ : ℝ → ℝ} {C m a b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hsub : Ioo a b ⊆ regularCornerDomain m)
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo a b), ρ t ≤ 1) :
    MonotoneOn (fun t => (firstTangency U t).1) (Ioo a b) ∧
      AntitoneOn (fun t => (firstTangency U t).2) (Ioo a b) := by
  have hpair : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, x ≤ y →
      (firstTangency U x).1 ≤ (firstTangency U y).1 ∧
        (firstTangency U y).2 ≤ (firstTangency U x).2 := by
    intro x hx y hy hxy
    have hclosed : Icc x y ⊆ regularCornerDomain m := by
      intro t ht
      exact hsub ⟨hx.1.trans_le ht.1, ht.2.trans_lt hy.2⟩
    have hdir := regularCornerDomain_interval_directions hclosed
    have hm := hU.firstTangency_monotone_of_unit_density hρ hρ0 hρC heq hxy
      (fun t ht => (hclosed ht).1) hdir.1 hdir.2
      (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hx.1.le hy.2.le) hunit)
    exact ⟨hm.1 (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy) hxy,
      hm.2 (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy) hxy⟩
  exact ⟨fun _ hx _ hy hxy => (hpair _ hx _ hy hxy).1,
    fun _ hx _ hy hxy => (hpair _ hx _ hy hxy).2⟩

theorem IsDownwardCap.secondTangency_monotoneOn_open_of_unit_density
    {U : Set Plane} (hU : IsDownwardCap U) {ρ : ℝ → ℝ} {C m a b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hsub : Ioo a b ⊆ regularCornerDomain m)
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo a b), ρ (t + Real.pi / 2) ≤ 1) :
    MonotoneOn (fun t => (secondTangency U t).1) (Ioo a b) ∧
      MonotoneOn (fun t => (secondTangency U t).2) (Ioo a b) := by
  have hpair : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, x ≤ y →
      (secondTangency U x).1 ≤ (secondTangency U y).1 ∧
        (secondTangency U x).2 ≤ (secondTangency U y).2 := by
    intro x hx y hy hxy
    have hclosed : Icc x y ⊆ regularCornerDomain m := by
      intro t ht
      exact hsub ⟨hx.1.trans_le ht.1, ht.2.trans_lt hy.2⟩
    have hdir := regularCornerDomain_interval_directions hclosed
    have hm := hU.secondTangency_monotone_of_unit_density hρ hρ0 hρC heq hxy
      (fun t ht => (hclosed ht).1) hdir.1 hdir.2
      (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hx.1.le hy.2.le) hunit)
    exact ⟨hm.1 (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy) hxy,
      hm.2 (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy) hxy⟩
  exact ⟨fun _ hx _ hy hxy => (hpair _ hx _ hy hxy).1,
    fun _ hx _ hy hxy => (hpair _ hx _ hy hxy).2⟩

end AmbidextrousSofa
