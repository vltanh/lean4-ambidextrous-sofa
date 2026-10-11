module

public import AmbidextrousSofa.Analysis.CornerEnergy
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

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
  simp only [firstTangency, attachedCorner_fst_eq_support, secondCornerVelocity, supportTangent,
    angleSupport_eq_imported_supp]
  ring

theorem firstTangency_snd_eq_support (U : Set Plane) (t : ℝ) :
    (firstTangency U t).2 = (angleSupport U t - 1) * Real.sin t +
      supportTangent U t * Real.cos t := by
  simp only [firstTangency, attachedCorner_snd_eq_support, secondCornerVelocity, supportTangent,
    angleSupport_eq_imported_supp]
  ring

theorem secondTangency_fst_eq_support (U : Set Plane) (t : ℝ) :
    (secondTangency U t).1 = -supportTangent U (t + Real.pi / 2) * Real.cos t -
      (angleSupport U (t + Real.pi / 2) - 1) * Real.sin t := by
  simp only [secondTangency, attachedCorner_fst_eq_support, firstCornerVelocity, supportTangent,
    angleSupport_eq_imported_supp]
  ring

theorem secondTangency_snd_eq_support (U : Set Plane) (t : ℝ) :
    (secondTangency U t).2 = -supportTangent U (t + Real.pi / 2) * Real.sin t +
      (angleSupport U (t + Real.pi / 2) - 1) * Real.cos t := by
  simp only [secondTangency, attachedCorner_snd_eq_support, firstCornerVelocity, supportTangent,
    angleSupport_eq_imported_supp]
  ring

theorem absolutelyContinuousOnInterval_monotoneOn_of_ae_hasDerivAt_nonneg
    {f d : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hab : a ≤ b)
    (hd : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt f (d t) t ∧ 0 ≤ d t) :
    MonotoneOn f (Icc a b) := by
  intro x hx y hy hxy
  have h := absolutelyContinuousOnInterval_le_initial_of_ae_deriv_nonpos (f := fun t => -f t)
    (hf.neg.mono (by rw [uIcc_of_le hab, uIcc_of_le hxy]; exact Icc_subset_Icc hx.1 hy.2)) hxy
    (by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hx.1 hy.2) hd]
        with t ht
      simpa [ht.1.deriv] using ht.2) (right_mem_Icc.mpr hxy)
  linarith

section Density

variable {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ} {C a b t : ℝ}
  (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
  (heq : (upperCurvature U).restrict S =
    (volume.restrict S).withDensity (fun x => ENNReal.ofReal (ρ x)))
include hU hρ hρ0 hρC heq

theorem IsDownwardCap.absolutelyContinuousOnInterval_tangency_coordinates_of_density
    (hab : a ≤ b) (hbase : Icc a b ⊆ S)
    (hshift : Icc (a + Real.pi / 2) (b + Real.pi / 2) ⊆ S) :
    AbsolutelyContinuousOnInterval (fun t => (firstTangency U t).1) a b ∧
      AbsolutelyContinuousOnInterval (fun t => (firstTangency U t).2) a b ∧
      AbsolutelyContinuousOnInterval (fun t => (secondTangency U t).1) a b ∧
      AbsolutelyContinuousOnInterval (fun t => (secondTangency U t).2) a b := by
  have h1 := (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval (a := a)
    (b := b)
  have hf := (hU.absolutelyContinuousOnInterval_angleSupport a b).sub h1
  have hg := (hU.absolutelyContinuousOnInterval_angleSupport_shift a b (Real.pi / 2)).sub h1
  have hft := hU.absolutelyContinuousOnInterval_supportTangent_of_density hρ hρ0 hρC heq hab hbase
  have hgt := hU.absolutelyContinuousOnInterval_supportTangent_shift_of_density
    hρ hρ0 hρC heq hab hshift
  have hs := Real.lipschitzWith_sin.lipschitzOnWith.absolutelyContinuousOnInterval (a := a) (b := b)
  have hc := Real.lipschitzWith_cos.lipschitzOnWith.absolutelyContinuousOnInterval (a := a) (b := b)
  simp only [firstTangency_fst_eq_support, firstTangency_snd_eq_support,
    secondTangency_fst_eq_support, secondTangency_snd_eq_support]
  exact ⟨(hf.mul hc).sub (hft.mul hs), (hf.mul hs).add (hft.mul hc),
    (hgt.neg.mul hc).sub (hg.mul hs), (hgt.neg.mul hs).add (hg.mul hc)⟩

theorem IsDownwardCap.ae_hasDerivAt_tangency_coordinates_of_density
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
  refine ⟨(hcx.add (hv.2.mul (Real.hasDerivAt_sin t))).congr_deriv ?_,
    (hcy.sub (hv.2.mul (Real.hasDerivAt_cos t))).congr_deriv ?_,
    (hcx.sub (hv.1.mul (Real.hasDerivAt_cos t))).congr_deriv ?_,
    (hcy.sub (hv.1.mul (Real.hasDerivAt_sin t))).congr_deriv ?_⟩ <;>
  simp only [cornerVelocityX, cornerVelocityY] <;> ring

/-- On a closed interval of the first quarter with regular directions, unit first density
makes the first tangency move right and down, and unit companion density makes the second
tangency move right and up. -/
theorem IsDownwardCap.tangency_monotone_of_unit_density
    (hab : a ≤ b) (hquarter : Icc a b ⊆ Ioo (0 : ℝ) (Real.pi / 2))
    (hbase : Icc a b ⊆ S) (hshift : Icc (a + Real.pi / 2) (b + Real.pi / 2) ⊆ S) :
    ((∀ᵐ t ∂volume.restrict (Ioo a b), ρ t ≤ 1) →
      MonotoneOn (fun t => (firstTangency U t).1) (Icc a b) ∧
        AntitoneOn (fun t => (firstTangency U t).2) (Icc a b)) ∧
    ((∀ᵐ t ∂volume.restrict (Ioo a b), ρ (t + Real.pi / 2) ≤ 1) →
      MonotoneOn (fun t => (secondTangency U t).1) (Icc a b) ∧
        MonotoneOn (fun t => (secondTangency U t).2) (Icc a b)) := by
  have hac := hU.absolutelyContinuousOnInterval_tangency_coordinates_of_density
    hρ hρ0 hρC heq hab hbase hshift
  have hd := hU.ae_hasDerivAt_tangency_coordinates_of_density hρ hρ0 hρC heq hab hbase hshift
  have hsc : ∀ᵐ t ∂volume.restrict (Ioo a b), 0 ≤ Real.sin t ∧ 0 ≤ Real.cos t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (sin_cos_pos_of_mem_quarter (hquarter (Ioo_subset_Icc_self ht))).imp le_of_lt le_of_lt
  have hmono {f d : ℝ → ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
      (hfd : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt f (d t) t ∧ 0 ≤ d t) :=
    absolutelyContinuousOnInterval_monotoneOn_of_ae_hasDerivAt_nonneg hf hab hfd
  constructor <;> intro hunit
  · exact ⟨hmono hac.1 (by filter_upwards [hd, hunit, hsc] with t hd hu hsc
      using ⟨hd.1, mul_nonneg (sub_nonneg.mpr hu) hsc.1⟩),
      by simpa using (hmono hac.2.1.neg (by filter_upwards [hd, hunit, hsc] with t hd hu hsc
        using ⟨hd.2.1.neg, by nlinarith⟩)).neg⟩
  · exact ⟨hmono hac.2.2.1 (by filter_upwards [hd, hunit, hsc] with t hd hu hsc
      using ⟨hd.2.2.1, mul_nonneg (sub_nonneg.mpr hu) hsc.2⟩),
      hmono hac.2.2.2 (by filter_upwards [hd, hunit, hsc] with t hd hu hsc
        using ⟨hd.2.2.2, mul_nonneg (sub_nonneg.mpr hu) hsc.1⟩)⟩

theorem IsDownwardCap.hasDerivAt_firstWall_angle_of_density
    (hbase : Icc a b ⊆ S) (ht : t ∈ Ioo a b) (hs : Real.sin t ≠ 0) (x : ℝ) :
    HasDerivAt (fun s => firstWall U s x)
      ((x - (firstTangency U t).1) / Real.sin t ^ 2) t := by
  refine ((((hU.hasDerivAt_angleSupport_of_density hρ hρ0 hρC heq hbase ht).sub_const 1).sub
    ((Real.hasDerivAt_cos t).const_mul x)).div (Real.hasDerivAt_sin t) hs).congr_deriv ?_
  simp only [Pi.sub_apply, firstTangency_fst_eq_support]
  congr 1
  linear_combination x * Real.sin_sq_add_cos_sq t

theorem IsDownwardCap.hasDerivAt_secondWall_angle_of_density
    (hshift : Icc (a + Real.pi / 2) (b + Real.pi / 2) ⊆ S)
    (ht : t ∈ Ioo a b) (hc : Real.cos t ≠ 0) (x : ℝ) :
    HasDerivAt (fun s => secondWall U s x)
      ((x - (secondTangency U t).1) / Real.cos t ^ 2) t := by
  simp only [secondWall, companionNormal_eq_unitNormal]
  refine ((((hU.hasDerivAt_angleSupport_shift_of_density hρ hρ0 hρC heq hshift ht).sub_const
    1).add ((Real.hasDerivAt_sin t).const_mul x)).div (Real.hasDerivAt_cos t) hc).congr_deriv ?_
  simp only [Pi.add_apply, secondTangency_fst_eq_support]
  congr 1
  linear_combination x * Real.sin_sq_add_cos_sq t

end Density

end AmbidextrousSofa
