module

public import AmbidextrousSofa.Analysis.JointSourceContacts
public import AmbidextrousSofa.Measure.RealRadonNikodym
public import Mathlib.MeasureTheory.Group.Measure

@[expose] public section

/-!
# Full angular density of the joint source limit

The structure `IsTiltedFirstUnitTarget` collects the hypotheses on the
target of the tilted first-unit case, under which the remaining files of
the joint source construction describe the common source limit.
Interval masses of the limit converge along the common filter, so on
every compact regular interval its angular mass is the actual curvature.
The common source measure has no mass at any exceptional normal, so its
angular marginal has the curvature density on the whole open upper
semicircle. All translated angular marginals are then absolutely
continuous with respect to Lebesgue measure. This transfers the actual
almost everywhere support calculus to each literal source branch.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

/-- The tilted first-unit case, for a target strictly inside the box `[a, b] × [0, 1]`: a full
maximum of height one on `[-2C, 2C]` with `1/2 < C`, whose middle half is affine of positive
slope `m`, from height `1 - h < 1` at `-C` to `1` at `C`, with a nonnegative curvature density
`ρ ≤ K` on the regular domain that is at most one on the first quarter. -/
structure IsTiltedFirstUnitTarget (target : Set Plane) (a b C h m c : ℝ) (ρ : ℝ → ℝ) (K : ℝ) :
    Prop where
  hU : IsFullCapMaximizer target
  hl : horizontalLeft target = -2 * C
  hr : horizontalRight target = 2 * C
  hC : 1 / 2 < C
  hm : 0 < m
  hheight : capHeight target = 1
  haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
    capRoof target x = m * x + c
  hlow : capRoof target (-C) = 1 - h
  hhigh : capRoof target C = 1
  hh : 0 < h
  hρ : Measurable ρ
  hρ0 : ∀ t, 0 ≤ ρ t
  hρK : ∀ t, ρ t ≤ K
  heq : (upperCurvature target).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t))
  hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1
  hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1
  hleft : a < horizontalLeft target
  hright : horizontalRight target < b

namespace IsTiltedFirstUnitTarget

variable {target : Set Plane} {a b C h m c K : ℝ} {ρ : ℝ → ℝ}
  (H : IsTiltedFirstUnitTarget target a b C h m c ρ K)
include H

/-- The middle window of the target is `(-C, C)`. -/
theorem middle_eq : Ioo (horizontalLeft target + capWidth target / 4)
    (horizontalRight target - capWidth target / 4) = Ioo (-C) C := by
  unfold capWidth; rw [H.hl, H.hr]; congr 1 <;> ring

theorem middleHalfInterval_eq :
    middleHalfInterval (horizontalLeft target) (horizontalRight target) = Icc (-C) C := by
  rw [middleHalfInterval, H.hl, H.hr]; congr 1 <;> ring

theorem Ioo_subset_box : Ioo (-C) C ⊆ Icc a b := fun x hx =>
  ⟨by linarith only [H.hleft, H.hl, hx.1, H.hC], by linarith only [H.hright, H.hr, hx.2, H.hC]⟩

theorem mem_horizontalProjection :
    -C ∈ horizontalProjection target ∧ C ∈ horizontalProjection target := by
  rw [horizontalProjection_eq_Icc H.hU.isCap.nonempty H.hU.isCap.isCompact H.hU.isCap.convex,
    H.hl, H.hr]
  exact ⟨⟨by linarith [H.hC], by linarith [H.hC]⟩, by linarith [H.hC], by linarith [H.hC]⟩

end IsTiltedFirstUnitTarget

theorem ae_regularCornerDomain_of_mem_quarter (m : ℝ) :
    ∀ᵐ t : ℝ ∂volume, t ∈ Ioo (0 : ℝ) (Real.pi / 2) → t ∈ regularCornerDomain m := by
  filter_upwards [volume.ae_ne (affineNormalAngle m),
    volume.ae_ne (affineNormalAngle m - Real.pi / 2)] with t ht htm hti
  refine ⟨hti, ⟨⟨hti.1, by linarith [hti.2, Real.pi_pos]⟩, ?_⟩,
    ⟨⟨by linarith [hti.1, Real.pi_pos], by linarith [hti.2]⟩, ?_⟩⟩ <;>
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
  · exact ⟨hti.2.ne, ht⟩
  · exact ⟨by linarith [hti.1], fun h => htm (by linarith)⟩

namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b C h m c K : ℝ} {ρ : ℝ → ℝ}
  (J : SelectedJointSourceLimit target a b)

theorem ae_angle_ne (θ : ℝ) : ∀ᵐ z ∂(J.measure : Measure Plane), z.1 ≠ θ := by
  simpa only [mem_prod, mem_singleton_iff, mem_univ, and_true] using
    measure_eq_zero_iff_ae_notMem.mp (J.angular_fiber_eq_zero θ)

/-- On a compact regular interval the selected source masses tend to the curvature, so the
angular marginal is the curvature on the regular domain; it has no atom at the two removed
normals. -/
theorem angularMeasure_eq_density (H : IsTiltedFirstUnitTarget target a b C h m c ρ K) :
    J.angularMeasure = (volume.restrict (Ioo (0 : ℝ) Real.pi)).withDensity
      (fun t => ENNReal.ofReal (ρ t)) := by
  have hIoc (s t : ℝ) (hst : s ≤ t) (hreg : Icc s t ⊆ regularCurvatureDomain m) :
      J.angularMeasure (Ioc s t) = upperCurvature target (Ioc s t) := by
    have hfrontier : (J.measure : Measure Plane) (frontier (Ioc s t ×ˢ (univ : Set ℝ))) = 0 := by
      rcases hst.lt_or_eq with hst | rfl
      · rw [frontier_prod_univ_eq, frontier_Ioc hst, insert_eq, union_prod]
        exact measure_union_null (J.angular_fiber_eq_zero s) (J.angular_fiber_eq_zero t)
      · simp
    rw [angularMeasure, Measure.map_apply measurable_fst measurableSet_Ioc, ← prod_univ]
    refine (measureReal_eq_measureReal_iff (measure_ne_top _ _) measure_Ioc_lt_top.ne).1
      (tendsto_nhds_unique (finiteMeasure_tendsto_real_apply_of_null_frontier J.converges
        hfrontier) ?_)
    exact ((innerAngularMass_Ioc_tendsto_of_canonical_maximum H.hU H.hheight H.haffine
      H.hTargetBox J.selected J.hausdorff J.level_tendsto (fun n => (J.coefficient_pos n).le)
      J.coefficient_tendsto H.hleft H.hright hst hreg).mono_left sourceLimitFilter_le_atTop).congr
        fun n => (J.finiteMeasure_real_prod_univ n measurableSet_Ioc).symm
  have hwing {u v : ℝ} (huv : Ioo u v ⊆ regularCurvatureDomain m) :
      J.angularMeasure.restrict (Ioo u v) = (upperCurvature target).restrict (Ioo u v) :=
    measure_restrict_Ioo_eq_of_Ioc fun s t hst hsub => hIoc s t hst (hsub.trans huv)
  have hself : J.angularMeasure.restrict (regularCurvatureDomain m) = J.angularMeasure := by
    refine Measure.restrict_eq_self_of_ae_mem ((ae_map_iff measurable_fst.aemeasurable
      (measurableSet_regularCurvatureDomain m)).mpr ?_)
    filter_upwards [J.ae_angle_mem_upper, J.ae_angle_ne (Real.pi / 2),
      J.ae_angle_ne (affineNormalAngle m)] with z hz htop haff
    exact ⟨hz, by simp [htop, haff]⟩
  have hvol : (volume : Measure ℝ).restrict (regularCurvatureDomain m) =
      volume.restrict (Ioo (0 : ℝ) Real.pi) :=
    Measure.restrict_congr_set (sdiff_null_ae_eq_self ((Set.toFinite _).measure_zero _))
  have hsub := (regularCurvatureDomain_eq_three m).ge
  rw [← hself, ← hvol, ← H.heq, regularCurvatureDomain_eq_three, Measure.restrict_union_congr,
    Measure.restrict_union_congr]
  exact ⟨⟨hwing fun x hx => hsub (.inl (.inl hx)), hwing fun x hx => hsub (.inl (.inr hx))⟩,
    hwing fun x hx => hsub (.inr hx)⟩

theorem angularMeasure_absolutelyContinuous
    (H : IsTiltedFirstUnitTarget target a b C h m c ρ K) : J.angularMeasure ≪ volume := by
  rw [J.angularMeasure_eq_density H]
  exact (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict

theorem shifted_angle_absolutelyContinuous (hac : J.angularMeasure ≪ volume) (d : ℝ) :
    (J.measure : Measure Plane).map (fun z => z.1 - d) ≪ (volume : Measure ℝ) := by
  have h := hac.map (measurable_sub_const' d)
  rw [map_sub_right_eq_self volume d] at h
  simpa only [angularMeasure, Measure.map_map (measurable_sub_const' d) measurable_fst,
    Function.comp_def] using h

theorem ae_shifted_angle_regularCorner (hac : J.angularMeasure ≪ volume) (d : ℝ) :
    ∀ᵐ z ∂(J.measure : Measure Plane),
      z.1 - d ∈ Ioo (0 : ℝ) (Real.pi / 2) → z.1 - d ∈ regularCornerDomain m :=
  ae_of_ae_map (measurable_fst.sub_const d).aemeasurable
    ((J.shifted_angle_absolutelyContinuous hac d).ae_le (ae_regularCornerDomain_of_mem_quarter m))

end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
