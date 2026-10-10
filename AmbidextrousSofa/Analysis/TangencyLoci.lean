import AmbidextrousSofa.Analysis.CornerEnergy
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Actual inner-wall tangency loci

The two loci are the actual attached corner displaced along its two
wall directions. Their coordinate derivatives are expressed in the
literal curvature density. These identities supply monotonicity only
on a quarter where the corresponding actual density is at most one.
The angular derivative of each wall is measured by its horizontal
distance from the appropriate tangency locus.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

def firstTangency (U : Set Plane) (t : ℝ) : Plane :=
  ((attachedCorner U t).1 + secondCornerVelocity U t * Real.sin t,
    (attachedCorner U t).2 - secondCornerVelocity U t * Real.cos t)

def secondTangency (U : Set Plane) (t : ℝ) : Plane :=
  ((attachedCorner U t).1 - firstCornerVelocity U t * Real.cos t,
    (attachedCorner U t).2 - firstCornerVelocity U t * Real.sin t)

theorem firstTangency_fst_eq_support (U : Set Plane) (t : ℝ) :
    (firstTangency U t).1 = (angleSupport U t - 1) * Real.cos t -
      supportTangent U t * Real.sin t := by
  rw [firstTangency, attachedCorner_fst_eq_support]
  change (angleSupport U t - 1) * Real.cos t -
      (angleSupport U (t + Real.pi / 2) - 1) * Real.sin t +
      (angleSupport U (t + Real.pi / 2) - supportTangent U t - 1) * Real.sin t = _
  ring

theorem firstTangency_snd_eq_support (U : Set Plane) (t : ℝ) :
    (firstTangency U t).2 = (angleSupport U t - 1) * Real.sin t +
      supportTangent U t * Real.cos t := by
  rw [firstTangency, attachedCorner_snd_eq_support]
  change (angleSupport U t - 1) * Real.sin t +
      (angleSupport U (t + Real.pi / 2) - 1) * Real.cos t -
      (angleSupport U (t + Real.pi / 2) - supportTangent U t - 1) * Real.cos t = _
  ring

theorem secondTangency_fst_eq_support (U : Set Plane) (t : ℝ) :
    (secondTangency U t).1 = -supportTangent U (t + Real.pi / 2) * Real.cos t -
      (angleSupport U (t + Real.pi / 2) - 1) * Real.sin t := by
  rw [secondTangency, attachedCorner_fst_eq_support]
  change (angleSupport U t - 1) * Real.cos t -
      (angleSupport U (t + Real.pi / 2) - 1) * Real.sin t -
      (angleSupport U t + supportTangent U (t + Real.pi / 2) - 1) * Real.cos t = _
  ring

theorem secondTangency_snd_eq_support (U : Set Plane) (t : ℝ) :
    (secondTangency U t).2 = -supportTangent U (t + Real.pi / 2) * Real.sin t +
      (angleSupport U (t + Real.pi / 2) - 1) * Real.cos t := by
  rw [secondTangency, attachedCorner_snd_eq_support]
  change (angleSupport U t - 1) * Real.sin t +
      (angleSupport U (t + Real.pi / 2) - 1) * Real.cos t -
      (angleSupport U t + supportTangent U (t + Real.pi / 2) - 1) * Real.sin t = _
  ring

theorem IsDownwardCap.absolutelyContinuousOnInterval_tangency_coordinates_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hab : a ≤ b) (hbase : Icc a b ⊆ S)
    (hshift : Icc (a + Real.pi / 2) (b + Real.pi / 2) ⊆ S) :
    AbsolutelyContinuousOnInterval (fun t => (firstTangency U t).1) a b ∧
      AbsolutelyContinuousOnInterval (fun t => (firstTangency U t).2) a b ∧
      AbsolutelyContinuousOnInterval (fun t => (secondTangency U t).1) a b ∧
      AbsolutelyContinuousOnInterval (fun t => (secondTangency U t).2) a b := by
  have hf := hU.absolutelyContinuousOnInterval_angleSupport a b
  have hg := hU.absolutelyContinuousOnInterval_angleSupport_shift a b (Real.pi / 2)
  have hft := hU.absolutelyContinuousOnInterval_supportTangent_of_density
    hρ hρ0 hρC heq hab hbase
  have hgt := hU.absolutelyContinuousOnInterval_supportTangent_shift_of_density
    hρ hρ0 hρC heq hab hshift
  have hs : AbsolutelyContinuousOnInterval Real.sin a b :=
    Real.lipschitzWith_sin.lipschitzOnWith.absolutelyContinuousOnInterval
  have hc : AbsolutelyContinuousOnInterval Real.cos a b :=
    Real.lipschitzWith_cos.lipschitzOnWith.absolutelyContinuousOnInterval
  have h1 : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b :=
    (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [funext (firstTangency_fst_eq_support U)]
    exact ((hf.sub h1).mul hc).sub (hft.mul hs)
  · rw [funext (firstTangency_snd_eq_support U)]
    exact ((hf.sub h1).mul hs).add (hft.mul hc)
  · rw [funext (secondTangency_fst_eq_support U)]
    exact (hgt.neg.mul hc).sub ((hg.sub h1).mul hs)
  · rw [funext (secondTangency_snd_eq_support U)]
    exact (hgt.neg.mul hs).add ((hg.sub h1).mul hc)

theorem IsDownwardCap.ae_hasDerivAt_tangency_coordinates_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hab : a ≤ b) (hbase : Icc a b ⊆ S)
    (hshift : Icc (a + Real.pi / 2) (b + Real.pi / 2) ⊆ S) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt (fun x => (firstTangency U x).1) ((1 - ρ t) * Real.sin t) t ∧
      HasDerivAt (fun x => (firstTangency U x).2) ((ρ t - 1) * Real.cos t) t ∧
      HasDerivAt (fun x => (secondTangency U x).1)
        ((1 - ρ (t + Real.pi / 2)) * Real.cos t) t ∧
      HasDerivAt (fun x => (secondTangency U x).2)
        ((1 - ρ (t + Real.pi / 2)) * Real.sin t) t := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    hU.ae_hasDerivAt_cornerVelocities_of_density hρ hρ0 hρC heq hab hbase hshift]
    with t ht hv
  have hcx := hU.hasDerivAt_attachedCorner_fst_of_density hρ hρ0 hρC heq hbase hshift ht
  have hcy := hU.hasDerivAt_attachedCorner_snd_of_density hρ hρ0 hρC heq hbase hshift ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (hcx.add (hv.2.mul (Real.hasDerivAt_sin t))).congr_deriv
    dsimp [cornerVelocityX]
    ring
  · apply (hcy.sub (hv.2.mul (Real.hasDerivAt_cos t))).congr_deriv
    dsimp [cornerVelocityY]
    ring
  · apply (hcx.sub (hv.1.mul (Real.hasDerivAt_cos t))).congr_deriv
    dsimp [cornerVelocityX]
    ring
  · apply (hcy.sub (hv.1.mul (Real.hasDerivAt_sin t))).congr_deriv
    dsimp [cornerVelocityY]
    ring

theorem absolutelyContinuousOnInterval_monotoneOn_of_ae_hasDerivAt_nonneg
    {f d : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hab : a ≤ b)
    (hd : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt f (d t) t ∧ 0 ≤ d t) :
    MonotoneOn f (Icc a b) := by
  intro x hx y hy hxy
  have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
  have hxyac : AbsolutelyContinuousOnInterval (fun t => -f t) x y :=
    hf.neg.mono (by simpa only [uIcc_of_le hab, uIcc_of_le hxy] using hsub)
  have hsign : ∀ᵐ t ∂volume.restrict (Ioo x y), deriv (fun s => -f s) t ≤ 0 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (Ioo_subset_Ioo hx.1 hy.2) hd] with t ht
    rw [ht.1.neg.deriv]
    exact neg_nonpos.mpr ht.2
  have h := absolutelyContinuousOnInterval_le_initial_of_ae_deriv_nonpos
    hxyac hxy hsign (right_mem_Icc.mpr hxy)
  linarith

theorem IsDownwardCap.firstTangency_monotone_of_unit_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hab : a ≤ b) (hquarter : Icc a b ⊆ Ioo (0 : ℝ) (Real.pi / 2))
    (hbase : Icc a b ⊆ S) (hshift : Icc (a + Real.pi / 2) (b + Real.pi / 2) ⊆ S)
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo a b), ρ t ≤ 1) :
    MonotoneOn (fun t => (firstTangency U t).1) (Icc a b) ∧
      AntitoneOn (fun t => (firstTangency U t).2) (Icc a b) := by
  have hac := hU.absolutelyContinuousOnInterval_tangency_coordinates_of_density
    hρ hρ0 hρC heq hab hbase hshift
  have hd := hU.ae_hasDerivAt_tangency_coordinates_of_density
    hρ hρ0 hρC heq hab hbase hshift
  constructor
  · apply absolutelyContinuousOnInterval_monotoneOn_of_ae_hasDerivAt_nonneg hac.1 hab
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hd, hunit] with t ht hd hu
    have htq := hquarter (Ioo_subset_Icc_self ht)
    exact ⟨hd.1, mul_nonneg (sub_nonneg.mpr hu)
      (Real.sin_nonneg_of_mem_Icc ⟨htq.1.le, by linarith [htq.2, Real.pi_pos]⟩)⟩
  · have hmono : MonotoneOn (fun t => -(firstTangency U t).2) (Icc a b) := by
      apply absolutelyContinuousOnInterval_monotoneOn_of_ae_hasDerivAt_nonneg hac.2.1.neg hab
      filter_upwards [ae_restrict_mem measurableSet_Ioo, hd, hunit] with t ht hd hu
      have htq := hquarter (Ioo_subset_Icc_self ht)
      refine ⟨hd.2.1.neg, ?_⟩
      apply neg_nonneg.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu)
        (Real.cos_nonneg_of_mem_Icc ⟨by linarith [htq.1, Real.pi_pos], htq.2.le⟩)
    intro x hx y hy hxy
    have h := hmono hx hy hxy
    linarith

theorem IsDownwardCap.secondTangency_monotone_of_unit_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hab : a ≤ b) (hquarter : Icc a b ⊆ Ioo (0 : ℝ) (Real.pi / 2))
    (hbase : Icc a b ⊆ S) (hshift : Icc (a + Real.pi / 2) (b + Real.pi / 2) ⊆ S)
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo a b), ρ (t + Real.pi / 2) ≤ 1) :
    MonotoneOn (fun t => (secondTangency U t).1) (Icc a b) ∧
      MonotoneOn (fun t => (secondTangency U t).2) (Icc a b) := by
  have hac := hU.absolutelyContinuousOnInterval_tangency_coordinates_of_density
    hρ hρ0 hρC heq hab hbase hshift
  have hd := hU.ae_hasDerivAt_tangency_coordinates_of_density
    hρ hρ0 hρC heq hab hbase hshift
  constructor
  · apply absolutelyContinuousOnInterval_monotoneOn_of_ae_hasDerivAt_nonneg hac.2.2.1 hab
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hd, hunit] with t ht hd hu
    have htq := hquarter (Ioo_subset_Icc_self ht)
    exact ⟨hd.2.2.1, mul_nonneg (sub_nonneg.mpr hu)
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [htq.1, Real.pi_pos], htq.2.le⟩)⟩
  · apply absolutelyContinuousOnInterval_monotoneOn_of_ae_hasDerivAt_nonneg hac.2.2.2 hab
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hd, hunit] with t ht hd hu
    have htq := hquarter (Ioo_subset_Icc_self ht)
    exact ⟨hd.2.2.2, mul_nonneg (sub_nonneg.mpr hu)
      (Real.sin_nonneg_of_mem_Icc ⟨htq.1.le, by linarith [htq.2, Real.pi_pos]⟩)⟩

theorem IsDownwardCap.hasDerivAt_firstWall_angle_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hbase : Icc a b ⊆ S) (ht : t ∈ Ioo a b) (hs : Real.sin t ≠ 0) (x : ℝ) :
    HasDerivAt (fun s => firstWall U s x)
      ((x - (firstTangency U t).1) / Real.sin t ^ 2) t := by
  have hf := hU.hasDerivAt_angleSupport_of_density hρ hρ0 hρC heq hbase ht
  have hd := ((hf.sub_const 1).sub ((Real.hasDerivAt_cos t).const_mul x)).div
    (Real.hasDerivAt_sin t) hs
  change HasDerivAt (fun s => firstWall U s x) _ t at hd
  apply hd.congr_deriv
  rw [firstTangency_fst_eq_support]
  apply congrArg (fun z : ℝ => z / Real.sin t ^ 2)
  nlinarith [congrArg (fun z : ℝ => x * z) (Real.sin_sq_add_cos_sq t)]

theorem IsDownwardCap.hasDerivAt_secondWall_angle_of_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b t : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hshift : Icc (a + Real.pi / 2) (b + Real.pi / 2) ⊆ S)
    (ht : t ∈ Ioo a b) (hc : Real.cos t ≠ 0) (x : ℝ) :
    HasDerivAt (fun s => secondWall U s x)
      ((x - (secondTangency U t).1) / Real.cos t ^ 2) t := by
  have hg := hU.hasDerivAt_angleSupport_shift_of_density hρ hρ0 hρC heq hshift ht
  have hd := ((hg.sub_const 1).add ((Real.hasDerivAt_sin t).const_mul x)).div
    (Real.hasDerivAt_cos t) hc
  have hfun : (fun s => (angleSupport U (s + Real.pi / 2) - 1 + x * Real.sin s) /
      Real.cos s) = fun s => secondWall U s x := by
    funext s
    simp only [secondWall, angleSupport, companionNormal_eq_unitNormal]
  rw [hfun] at hd
  apply hd.congr_deriv
  rw [secondTangency_fst_eq_support]
  apply congrArg (fun z : ℝ => z / Real.cos t ^ 2)
  nlinarith [congrArg (fun z : ℝ => x * z) (Real.sin_sq_add_cos_sq t)]

end AmbidextrousSofa
