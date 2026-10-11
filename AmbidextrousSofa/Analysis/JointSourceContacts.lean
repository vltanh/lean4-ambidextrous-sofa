module

public import AmbidextrousSofa.Analysis.JointSourceContactLimit
public import AmbidextrousSofa.Analysis.PositiveWallContacts

@[expose] public section

/-!
# Actual wall contacts supporting the common source measure

Cross-multiplied wall equations remain continuous at the axis normals.
The opposite-wall inequalities are encoded by continuous nonnegative
errors, with the cosine sign selecting the appropriate source family.
Every literal finite source has zero error. Their common limit therefore
satisfies the actual wall equation and the opposite-wall inequality.
Positive regular contacts can then be classified as a strict tangent
or an equal-wall corner, without an additional occupation hypothesis.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

def sourceWallResidual (U : Set Plane) (y θ x : ℝ) : ℝ :=
  support U (unitNormal θ) - 1 - x * Real.cos θ - y * Real.sin θ

def sourceForwardDefect (U : Set Plane) (y θ x : ℝ) : ℝ :=
  max (Real.cos θ) 0 * max (-sourceWallResidual U y (θ + Real.pi / 2) x) 0

def sourceBackwardDefect (U : Set Plane) (y θ x : ℝ) : ℝ :=
  max (-Real.cos θ) 0 * max (-sourceWallResidual U y (θ - Real.pi / 2) x) 0

theorem sourceWallResidual_add_half_pi (U : Set Plane) (y θ x : ℝ) :
    sourceWallResidual U y (θ + Real.pi / 2) x =
      support U (companionNormal θ) - 1 + x * Real.sin θ - y * Real.cos θ := by
  rw [sourceWallResidual, ← companionNormal_eq_unitNormal]
  simp only [Real.cos_add, Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two,
    mul_zero, mul_one, zero_sub, zero_add, mul_neg, sub_neg_eq_add]

theorem CapHausdorffTendsto.sourceWallResidual_tendsto
    {U : ℕ → Set Plane} {target : Set Plane} (h : CapHausdorffTendsto U target)
    (hU : ∀ n, IsDownwardCap (U n)) (hTarget : IsDownwardCap target)
    {height angle point : ℕ → ℝ} {y θ x : ℝ}
    (hy : Tendsto height atTop (𝓝 y)) (hθ : Tendsto angle atTop (𝓝 θ))
    (hx : Tendsto point atTop (𝓝 x)) :
    Tendsto (fun n => sourceWallResidual (U n) (height n) (angle n) (point n)) atTop
      (𝓝 (sourceWallResidual target y θ x)) := by
  have hs := (continuous_capSupport.tendsto (hTarget.toCompactCap, unitNormal θ)).comp
    ((IsDownwardCap.tendsto_toCompactCap hU hTarget h).prodMk_nhds
      ((continuous_unitNormal.tendsto θ).comp hθ))
  exact ((hs.sub_const 1).sub (hx.mul ((Real.continuous_cos.tendsto θ).comp hθ))).sub
    (hy.mul ((Real.continuous_sin.tendsto θ).comp hθ))

namespace AngularGrid

open FinitePolygon

/-- Every literal finite source lies on its own wall, below the opposite wall. -/
theorem innerSource_wall_defects_zero (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex grid) {x : ℝ} (hx : x ∈ innerSourceSet U grid j) :
    let y := finiteBarrier U (normal grid) (pairList grid) none x
    sourceWallResidual U y (fullAngle grid j) x = 0 ∧
      sourceForwardDefect U y (fullAngle grid j) x = 0 ∧
        sourceBackwardDefect U y (fullAngle grid j) x = 0 := by
  intro y
  have hy : y = supportWall U (normal grid j) x := innerSource_height U grid j hx
  have hR : sourceWallResidual U y (fullAngle grid j) x = 0 := by
    rw [normal_eq_unitNormal, supportWall_unitNormal, firstWall,
      eq_div_iff (Real.sin_pos_of_mem_Ioo (fullAngle_mem grid j)).ne'] at hy
    unfold sourceWallResidual
    linarith
  refine ⟨hR, ?_⟩
  cases j with
  | inl t =>
    rw [fullAngle]
    have ht := interiorPoint_mem grid t
    have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ht.2⟩
    have hother := first_source_le_companion U grid t hx
    rw [supportWall_companionNormal] at hother
    have h := (le_div_iff₀ hc).mp (hy.trans_le hother)
    have hn : 0 ≤ sourceWallResidual U y (t + Real.pi / 2) x := by
      rw [sourceWallResidual_add_half_pi]
      linarith
    exact ⟨by rw [sourceForwardDefect, max_eq_right (neg_nonpos.mpr hn), mul_zero],
      by rw [sourceBackwardDefect, max_eq_right (neg_nonpos.mpr hc.le), zero_mul]⟩
  | inr t =>
    rw [fullAngle]
    have ht := interiorPoint_mem grid t
    have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [Real.pi_pos])
    have hother := second_source_le_first U grid t hx
    rw [supportWall_unitNormal] at hother
    have h := (le_div_iff₀ hs).mp (hy.trans_le hother)
    have hn : 0 ≤ sourceWallResidual U y t x := by
      unfold sourceWallResidual
      linarith
    exact ⟨by rw [sourceForwardDefect, Real.cos_add_pi_div_two,
        max_eq_right (neg_nonpos.mpr hs.le), zero_mul],
      by rw [sourceBackwardDefect, add_sub_cancel_right, max_eq_right (neg_nonpos.mpr hn),
        mul_zero]⟩

namespace SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

theorem ae_wall_residuals (hTarget : IsDownwardCap target) :
    ∀ᵐ z ∂(J.measure : Measure Plane),
      sourceWallResidual target (sweptNiche target (Real.pi / 2) z.2) z.1 z.2 = 0 ∧
        sourceForwardDefect target (sweptNiche target (Real.pi / 2) z.2) z.1 z.2 = 0 ∧
          sourceBackwardDefect target (sweptNiche target (Real.pi / 2) z.2) z.1 z.2 = 0 := by
  set N := sweptNiche target (Real.pi / 2)
  have hF0 (U : Set Plane) (y θ x : ℝ) : 0 ≤ sourceForwardDefect U y θ x :=
    mul_nonneg (le_max_right _ _) (le_max_right _ _)
  have hB0 (U : Set Plane) (y θ x : ℝ) : 0 ≤ sourceBackwardDefect U y θ x :=
    mul_nonneg (le_max_right _ _) (le_max_right _ _)
  have hzero := J.ae_zero_of_source_limits (f := fun z => |sourceWallResidual target (N z.2) z.1 z.2|
      + sourceForwardDefect target (N z.2) z.1 z.2 + sourceBackwardDefect target (N z.2) z.1 z.2)
    (by
      have := continuous_support hTarget.isCompact
      have := continuous_unitNormal
      have hcomp := continuous_capSweptNiche.comp
        ((continuous_const : Continuous (fun _ : ℝ => hTarget.toCompactCap)).prodMk continuous_id)
      have : Continuous N := hcomp
      unfold sourceForwardDefect sourceBackwardDefect sourceWallResidual
      fun_prop)
    (fun _ => add_nonneg (add_nonneg (abs_nonneg _) (hF0 ..)) (hB0 ..))
    fun seq hseq point hpoint z hz => by
      have hH : CapHausdorffTendsto (fun n => J.caps (seq n)) target := J.hausdorff.comp hseq
      have hh := finiteBarrier_dyadic_tendsto hH (fun n => J.isCap (seq n))
        hTarget (J.level_tendsto.comp hseq) (fun n => (J.selected (seq n)).inBox)
        (fun n => (J.finiteSourceTags_subset_box (seq n) (hpoint n)).2) hz.snd_nhds
      have hR {d : ℕ → ℝ} {θ : ℝ} (hd : Tendsto d atTop (𝓝 θ)) :=
        hH.sourceWallResidual_tendsto (fun n => J.isCap (seq n)) hTarget hh hd hz.snd_nhds
      have hcos := (Real.continuous_cos.tendsto z.1).comp hz.fst_nhds
      have h0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
      refine tendsto_nhds_unique (((hR hz.fst_nhds).abs.add ((hcos.max h0).mul
        ((hR (hz.fst_nhds.add_const _)).neg.max h0))).add ((hcos.neg.max h0).mul
          ((hR (hz.fst_nhds.sub_const _)).neg.max h0))) (h0.congr fun n => ?_)
      obtain ⟨-, j, hθ, hs⟩ := hpoint n
      obtain ⟨h1, h2, h3⟩ := innerSource_wall_defects_zero _ _ j hs
      simp only [sourceForwardDefect, sourceBackwardDefect] at h2 h3
      simp only [Function.comp_apply, hθ, h1, h2, h3, abs_zero, add_zero]
  filter_upwards [hzero] with z hz
  have := abs_nonneg (sourceWallResidual target (N z.2) z.1 z.2)
  have := hF0 target (N z.2) z.1 z.2
  have := hB0 target (N z.2) z.1 z.2
  exact ⟨abs_eq_zero.mp (by linarith), by linarith, by linarith⟩

theorem ae_first_wall_contact (hTarget : IsDownwardCap target) :
    ∀ᵐ z ∂(J.measure : Measure Plane), z.1 ∈ Ioo (0 : ℝ) (Real.pi / 2) →
      firstWall target z.1 z.2 = sweptNiche target (Real.pi / 2) z.2 ∧
        fullWallClip hTarget.toCompactCap z.2 z.1 = sweptNiche target (Real.pi / 2) z.2 := by
  filter_upwards [J.ae_wall_residuals hTarget] with z ⟨hR, hF, _⟩ ht
  have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  rw [sourceForwardDefect, max_eq_left hc.le, mul_eq_zero, max_eq_right_iff, neg_nonpos,
    sourceWallResidual_add_half_pi] at hF
  have hfirst : firstWall target z.1 z.2 = sweptNiche target (Real.pi / 2) z.2 := by
    rw [firstWall, div_eq_iff hs.ne']
    unfold sourceWallResidual at hR
    linarith
  have hsecond : sweptNiche target (Real.pi / 2) z.2 ≤ secondWall target z.1 z.2 := by
    rw [secondWall, le_div_iff₀ hc]
    linarith [hF.resolve_left hc.ne']
  refine ⟨hfirst, ?_⟩
  change max (min (firstWall target z.1 z.2) (secondWall target z.1 z.2)) 0 = _
  rw [hfirst, min_eq_left hsecond, max_eq_left (sweptNiche_nonneg _ _ _)]

theorem ae_second_wall_contact (hTarget : IsDownwardCap target) :
    ∀ᵐ z ∂(J.measure : Measure Plane), z.1 ∈ Ioo (Real.pi / 2) Real.pi →
      secondWall target (z.1 - Real.pi / 2) z.2 = sweptNiche target (Real.pi / 2) z.2 ∧
        fullWallClip hTarget.toCompactCap z.2 (z.1 - Real.pi / 2) =
          sweptNiche target (Real.pi / 2) z.2 := by
  filter_upwards [J.ae_wall_residuals hTarget] with z ⟨hR, _, hB⟩ ht
  set t := z.1 - Real.pi / 2
  have hθ : z.1 = t + Real.pi / 2 := (sub_add_cancel _ _).symm
  have hs := Real.sin_pos_of_pos_of_lt_pi (x := t) (by linarith [ht.1])
    (by linarith [ht.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo (x := t) ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2]⟩
  rw [hθ, sourceWallResidual_add_half_pi] at hR
  rw [sourceBackwardDefect, hθ, add_sub_cancel_right, Real.cos_add_pi_div_two, neg_neg,
    max_eq_left hs.le, mul_eq_zero, max_eq_right_iff, neg_nonpos] at hB
  have hsecond : secondWall target t z.2 = sweptNiche target (Real.pi / 2) z.2 := by
    rw [secondWall, div_eq_iff hc.ne']
    linarith
  have hfirst : sweptNiche target (Real.pi / 2) z.2 ≤ firstWall target t z.2 := by
    rw [firstWall, le_div_iff₀ hs]
    unfold sourceWallResidual at hB
    linarith [hB.resolve_left hs.ne']
  refine ⟨hsecond, ?_⟩
  change max (min (firstWall target t z.2) (secondWall target t z.2)) 0 = _
  rw [hsecond, min_eq_right hfirst, max_eq_left (sweptNiche_nonneg _ _ _)]

end SelectedJointSourceLimit
end AngularGrid
end AmbidextrousSofa
