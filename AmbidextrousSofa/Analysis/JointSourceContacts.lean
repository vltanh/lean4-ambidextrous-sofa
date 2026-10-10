import AmbidextrousSofa.Analysis.JointSourceContactLimit
import AmbidextrousSofa.Analysis.PositiveWallContacts

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
    mul_zero, mul_one, zero_sub, add_zero, zero_add, mul_neg, sub_neg_eq_add]

theorem CapHausdorffTendsto.sourceWallResidual_tendsto
    {U : ℕ → Set Plane} {target : Set Plane} (h : CapHausdorffTendsto U target)
    (hU : ∀ n, IsDownwardCap (U n)) (hTarget : IsDownwardCap target)
    {height angle point : ℕ → ℝ} {y θ x : ℝ}
    (hy : Tendsto height atTop (𝓝 y)) (hθ : Tendsto angle atTop (𝓝 θ))
    (hx : Tendsto point atTop (𝓝 x)) :
    Tendsto (fun n => sourceWallResidual (U n) (height n) (angle n) (point n)) atTop
      (𝓝 (sourceWallResidual target y θ x)) := by
  have hcap := IsDownwardCap.tendsto_toCompactCap hU hTarget h
  have hn := (continuous_unitNormal.tendsto θ).comp hθ
  have hs := (continuous_capSupport.tendsto (hTarget.toCompactCap, unitNormal θ)).comp
    (hcap.prodMk_nhds hn)
  exact ((hs.sub_const 1).sub (hx.mul ((Real.continuous_cos.tendsto θ).comp hθ))).sub
    (hy.mul ((Real.continuous_sin.tendsto θ).comp hθ))

namespace AngularGrid

open FinitePolygon

theorem innerSource_wallResidual_zero (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex grid) {x : ℝ} (hx : x ∈ innerSourceSet U grid j) :
    sourceWallResidual U (finiteBarrier U (normal grid) (pairList grid) none x)
      (fullAngle grid j) x = 0 := by
  have hsource := innerSource_height U grid j hx
  rw [normal_eq_unitNormal, supportWall_unitNormal] at hsource
  have hs := Real.sin_pos_of_pos_of_lt_pi (fullAngle_mem grid j).1 (fullAngle_mem grid j).2
  have heq := (eq_div_iff hs.ne').mp hsource
  dsimp only [sourceWallResidual]
  linarith only [heq]

theorem innerSource_forwardDefect_zero (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex grid) {x : ℝ} (hx : x ∈ innerSourceSet U grid j) :
    sourceForwardDefect U (finiteBarrier U (normal grid) (pairList grid) none x)
      (fullAngle grid j) x = 0 := by
  cases j with
  | inl t =>
    have ht := interiorPoint_mem grid t
    have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
    have hsource := innerSource_height U grid (Sum.inl t) hx
    have hother := first_source_le_companion U grid t hx
    simp only [normal, supportWall_unitNormal] at hsource
    rw [supportWall_unitNormal, supportWall_companionNormal] at hother
    have hn : 0 ≤ sourceWallResidual U
        (finiteBarrier U (normal grid) (pairList grid) none x)
        ((t.val : ℝ) + Real.pi / 2) x := by
      rw [sourceWallResidual_add_half_pi]
      have hh := (le_div_iff₀ hc).mp (hsource.le.trans hother)
      linarith only [hh]
    simp only [sourceForwardDefect, fullAngle, max_eq_right (neg_nonpos.mpr hn), mul_zero]
  | inr t =>
    have ht := interiorPoint_mem grid t
    have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith only [ht.2, Real.pi_pos])
    simp only [sourceForwardDefect, fullAngle, Real.cos_add, Real.cos_pi_div_two,
      Real.sin_pi_div_two, mul_zero, mul_one, zero_sub,
      max_eq_right (neg_nonpos.mpr hs.le), zero_mul]

theorem innerSource_backwardDefect_zero (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex grid) {x : ℝ} (hx : x ∈ innerSourceSet U grid j) :
    sourceBackwardDefect U (finiteBarrier U (normal grid) (pairList grid) none x)
      (fullAngle grid j) x = 0 := by
  cases j with
  | inl t =>
    have ht := interiorPoint_mem grid t
    have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
    simp only [sourceBackwardDefect, fullAngle, max_eq_right (neg_nonpos.mpr hc.le), zero_mul]
  | inr t =>
    have ht := interiorPoint_mem grid t
    have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith only [ht.2, Real.pi_pos])
    have hsource := innerSource_height U grid (Sum.inr t) hx
    have hother := second_source_le_first U grid t hx
    simp only [normal, supportWall_companionNormal] at hsource
    rw [supportWall_companionNormal, supportWall_unitNormal] at hother
    have hn : 0 ≤ sourceWallResidual U
        (finiteBarrier U (normal grid) (pairList grid) none x) (t.val : ℝ) x := by
      have hh := (le_div_iff₀ hs).mp (hsource.le.trans hother)
      dsimp only [sourceWallResidual]
      linarith only [hh]
    simp only [sourceBackwardDefect, fullAngle, add_sub_cancel_right,
      max_eq_right (neg_nonpos.mpr hn), mul_zero]

namespace SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

theorem wall_residuals_eq_zero_of_source_limit
    (hTarget : IsDownwardCap target)
    (seq : ℕ → ℕ) (hseq : Tendsto seq atTop atTop)
    (point : ℕ → Plane) (hpoint : ∀ n, point n ∈ J.finiteSourceTags (seq n))
    (z : Plane) (hz : Tendsto point atTop (𝓝 z)) :
    sourceWallResidual target (sweptNiche target (Real.pi / 2) z.2) z.1 z.2 = 0 ∧
      sourceForwardDefect target (sweptNiche target (Real.pi / 2) z.2) z.1 z.2 = 0 ∧
        sourceBackwardDefect target (sweptNiche target (Real.pi / 2) z.2) z.1 z.2 = 0 := by
  let height : ℕ → ℝ := fun n => finiteBarrier (J.caps (seq n))
    (normal (dyadic (J.level (seq n)))) (pairList (dyadic (J.level (seq n)))) none (point n).2
  have hh : Tendsto height atTop (𝓝 (sweptNiche target (Real.pi / 2) z.2)) :=
    finiteBarrier_dyadic_tendsto (J.hausdorff.comp hseq) (fun n => J.isCap (seq n))
      hTarget (J.level_tendsto.comp hseq) (fun n => (J.selected (seq n)).inBox)
      (fun n => (J.finiteSourceTags_subset_box (seq n) (hpoint n)).2) hz.snd
  have hR := (J.hausdorff.comp hseq).sourceWallResidual_tendsto
    (fun n => J.isCap (seq n)) hTarget hh hz.fst hz.snd
  have hplus := (J.hausdorff.comp hseq).sourceWallResidual_tendsto
    (fun n => J.isCap (seq n)) hTarget hh (hz.fst.add_const (Real.pi / 2)) hz.snd
  have hminus := (J.hausdorff.comp hseq).sourceWallResidual_tendsto
    (fun n => J.isCap (seq n)) hTarget hh (hz.fst.sub_const (Real.pi / 2)) hz.snd
  have hcos := (Real.continuous_cos.tendsto z.1).comp hz.fst
  have hF := (hcos.max tendsto_const_nhds).mul (hplus.neg.max tendsto_const_nhds)
  have hB := (hcos.neg.max tendsto_const_nhds).mul (hminus.neg.max tendsto_const_nhds)
  have hzeroR (n : ℕ) : sourceWallResidual (J.caps (seq n)) (height n)
      (point n).1 (point n).2 = 0 := by
    obtain ⟨_hx, j, hθ, hsource⟩ := hpoint n
    rw [hθ]
    exact innerSource_wallResidual_zero _ _ j hsource
  have hzeroF (n : ℕ) : sourceForwardDefect (J.caps (seq n)) (height n)
      (point n).1 (point n).2 = 0 := by
    obtain ⟨_hx, j, hθ, hsource⟩ := hpoint n
    rw [hθ]
    exact innerSource_forwardDefect_zero _ _ j hsource
  have hzeroB (n : ℕ) : sourceBackwardDefect (J.caps (seq n)) (height n)
      (point n).1 (point n).2 = 0 := by
    obtain ⟨_hx, j, hθ, hsource⟩ := hpoint n
    rw [hθ]
    exact innerSource_backwardDefect_zero _ _ j hsource
  refine ⟨tendsto_nhds_unique hR ?_, tendsto_nhds_unique hF ?_, tendsto_nhds_unique hB ?_⟩
  · exact tendsto_const_nhds.congr' (Eventually.of_forall hzeroR).symm
  · exact tendsto_const_nhds.congr' (Eventually.of_forall hzeroF).symm
  · exact tendsto_const_nhds.congr' (Eventually.of_forall hzeroB).symm

theorem ae_wall_residuals (hTarget : IsDownwardCap target) :
    ∀ᵐ z ∂(J.measure : Measure Plane),
      sourceWallResidual target (sweptNiche target (Real.pi / 2) z.2) z.1 z.2 = 0 ∧
        sourceForwardDefect target (sweptNiche target (Real.pi / 2) z.2) z.1 z.2 = 0 ∧
          sourceBackwardDefect target (sweptNiche target (Real.pi / 2) z.2) z.1 z.2 = 0 := by
  let n : ℝ → ℝ := sweptNiche target (Real.pi / 2)
  let f : Plane → ℝ := fun z =>
    |sourceWallResidual target (n z.2) z.1 z.2| +
      sourceForwardDefect target (n z.2) z.1 z.2 +
        sourceBackwardDefect target (n z.2) z.1 z.2
  have hn : Continuous n :=
    continuous_capSweptNiche.comp
      ((continuous_const : Continuous (fun _ : ℝ => hTarget.toCompactCap)).prodMk continuous_id)
  have hR (d : ℝ) : Continuous (fun z : Plane =>
      sourceWallResidual target (n z.2) (z.1 + d) z.2) := by
    have hs := (continuous_angleSupport hTarget.isCompact).comp (continuous_fst.add_const d)
    change Continuous (fun z : Plane => angleSupport target (z.1 + d) - 1 -
      z.2 * Real.cos (z.1 + d) - n z.2 * Real.sin (z.1 + d))
    exact ((hs.sub continuous_const).sub
      (continuous_snd.mul (Real.continuous_cos.comp (continuous_fst.add_const d)))).sub
      ((hn.comp continuous_snd).mul (Real.continuous_sin.comp (continuous_fst.add_const d)))
  have hR0 : Continuous (fun z : Plane => sourceWallResidual target (n z.2) z.1 z.2) := by
    simpa only [add_zero] using hR 0
  have hRm : Continuous (fun z : Plane =>
      sourceWallResidual target (n z.2) (z.1 - Real.pi / 2) z.2) := by
    simpa only [sub_eq_add_neg] using hR (-(Real.pi / 2))
  have hf : Continuous f := by
    exact (hR0.abs.add
      (((Real.continuous_cos.comp continuous_fst).max continuous_const).mul
        ((hR (Real.pi / 2)).neg.max continuous_const))).add
      ((((Real.continuous_cos.comp continuous_fst).neg).max continuous_const).mul
        (hRm.neg.max continuous_const))
  have hf0 : ∀ z, 0 ≤ f z := fun z =>
    add_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg (le_max_right _ _) (le_max_right _ _)))
      (mul_nonneg (le_max_right _ _) (le_max_right _ _))
  have hzero := J.ae_zero_of_source_limits hf hf0 (by
    intro seq hseq point hpoint z hz
    obtain ⟨hRz, hFz, hBz⟩ := J.wall_residuals_eq_zero_of_source_limit
      hTarget seq hseq point hpoint z hz
    simp only [f, n, hRz, hFz, hBz, abs_zero, add_zero])
  filter_upwards [hzero] with z hz
  have hF0 : 0 ≤ sourceForwardDefect target (n z.2) z.1 z.2 :=
    mul_nonneg (le_max_right _ _) (le_max_right _ _)
  have hB0 : 0 ≤ sourceBackwardDefect target (n z.2) z.1 z.2 :=
    mul_nonneg (le_max_right _ _) (le_max_right _ _)
  dsimp only [f] at hz
  have habs := abs_nonneg (sourceWallResidual target (n z.2) z.1 z.2)
  exact ⟨abs_eq_zero.mp (by linarith), by linarith, by linarith⟩

theorem ae_first_wall_contact (hTarget : IsDownwardCap target) :
    ∀ᵐ z ∂(J.measure : Measure Plane), z.1 ∈ Ioo (0 : ℝ) (Real.pi / 2) →
      firstWall target z.1 z.2 = sweptNiche target (Real.pi / 2) z.2 ∧
        fullWallClip hTarget.toCompactCap z.2 z.1 = sweptNiche target (Real.pi / 2) z.2 := by
  filter_upwards [J.ae_wall_residuals hTarget] with z hz
  intro ht
  have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith only [ht.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
  have hfirst : firstWall target z.1 z.2 = sweptNiche target (Real.pi / 2) z.2 := by
    apply (div_eq_iff hs.ne').mpr
    dsimp only [sourceWallResidual] at hz
    linarith only [hz.1]
  have hother : 0 ≤ sourceWallResidual target (sweptNiche target (Real.pi / 2) z.2)
      (z.1 + Real.pi / 2) z.2 := by
    have hF := hz.2.1
    rw [sourceForwardDefect, max_eq_left hc.le] at hF
    have hm := (mul_eq_zero.mp hF).resolve_left hc.ne'
    have hle := le_max_left
      (-sourceWallResidual target (sweptNiche target (Real.pi / 2) z.2)
        (z.1 + Real.pi / 2) z.2) 0
    rw [hm] at hle
    linarith only [hle]
  have hsecond : sweptNiche target (Real.pi / 2) z.2 ≤ secondWall target z.1 z.2 := by
    apply (le_div_iff₀ hc).mpr
    rw [sourceWallResidual_add_half_pi] at hother
    linarith only [hother]
  refine ⟨hfirst, ?_⟩
  change max (min (firstWall target z.1 z.2) (secondWall target z.1 z.2)) 0 = _
  rw [hfirst, min_eq_left hsecond, max_eq_left (sweptNiche_nonneg _ _ _)]

theorem ae_second_wall_contact (hTarget : IsDownwardCap target) :
    ∀ᵐ z ∂(J.measure : Measure Plane), z.1 ∈ Ioo (Real.pi / 2) Real.pi →
      secondWall target (z.1 - Real.pi / 2) z.2 = sweptNiche target (Real.pi / 2) z.2 ∧
        fullWallClip hTarget.toCompactCap z.2 (z.1 - Real.pi / 2) =
          sweptNiche target (Real.pi / 2) z.2 := by
  filter_upwards [J.ae_wall_residuals hTarget] with z hz
  intro ht
  let t := z.1 - Real.pi / 2
  have hθ : z.1 = t + Real.pi / 2 := by dsimp only [t]; ring
  have hti : t ∈ Ioo (0 : ℝ) (Real.pi / 2) := by
    dsimp only [t]
    constructor <;> linarith only [ht.1, ht.2]
  have hs := Real.sin_pos_of_pos_of_lt_pi hti.1 (by linarith only [hti.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith only [hti.1, Real.pi_pos], hti.2⟩
  have hsecond : secondWall target t z.2 = sweptNiche target (Real.pi / 2) z.2 := by
    apply (div_eq_iff hc.ne').mpr
    have hR := hz.1
    rw [hθ, sourceWallResidual_add_half_pi] at hR
    linarith only [hR]
  have hother : 0 ≤ sourceWallResidual target (sweptNiche target (Real.pi / 2) z.2) t z.2 := by
    have hB := hz.2.2
    rw [sourceBackwardDefect, hθ] at hB
    simp only [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, mul_one,
      zero_sub, neg_neg, add_sub_cancel_right, max_eq_left hs.le] at hB
    have hm := (mul_eq_zero.mp hB).resolve_left hs.ne'
    have hle := le_max_left
      (-sourceWallResidual target (sweptNiche target (Real.pi / 2) z.2) t z.2) 0
    rw [hm] at hle
    linarith only [hle]
  have hfirst : sweptNiche target (Real.pi / 2) z.2 ≤ firstWall target t z.2 := by
    apply (le_div_iff₀ hs).mpr
    dsimp only [sourceWallResidual] at hother
    linarith only [hother]
  refine ⟨hsecond, ?_⟩
  change max (min (firstWall target t z.2) (secondWall target t z.2)) 0 = _
  rw [hsecond, min_eq_right hfirst, max_eq_left (sweptNiche_nonneg _ _ _)]

end SelectedJointSourceLimit
end AngularGrid
end AmbidextrousSofa
