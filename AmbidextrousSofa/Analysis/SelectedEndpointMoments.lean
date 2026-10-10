import AmbidextrousSofa.Analysis.ErosionMoments
import AmbidextrousSofa.Analysis.SelectedCurvature

/-!
# Endpoint estimates for the actual selected polygons

The abstract finite variation theorems are instantiated with the proved
dyadic selected polygons and their persistent support penalty. A fixed
containing box supplies an explicit uniform error, tending to zero with
the selection coefficient. Positive end faces allow an actual outward
variation inside the box; zero end faces are handled by a positive part.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem abs_coordDot_unitNormal_le_box {a b : ℝ} {p : Plane}
    (hp : p ∈ Icc a b ×ˢ Icc (0 : ℝ) 1) (t : ℝ) :
    |coordDot p (unitNormal t)| ≤ |a| + |b| + 1 := by
  have hx : |p.1| ≤ |a| + |b| := abs_le.mpr
    ⟨by linarith [hp.1.1, neg_abs_le a, abs_nonneg b],
      by linarith [hp.1.2, le_abs_self b, abs_nonneg a]⟩
  have hy : |p.2| ≤ 1 := by rw [abs_of_nonneg hp.2.1]; exact hp.2.2
  calc
    |coordDot p (unitNormal t)| ≤
        |p.1| * |Real.cos t| + |p.2| * |Real.sin t| := by
      simpa only [coordDot, unitNormal, abs_mul] using
        abs_add_le (p.1 * Real.cos t) (p.2 * Real.sin t)
    _ ≤ |p.1| + |p.2| := by
      have hc := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one t) (abs_nonneg p.1)
      have hs := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one t) (abs_nonneg p.2)
      simpa only [mul_one] using add_le_add hc hs
    _ ≤ |a| + |b| + 1 := by linarith

namespace AngularGrid

open FinitePolygon

def endpointSelectionError (a b coefficient : ℝ) : ℝ :=
  8 * (|a| + |b| + 1) * coefficient

theorem endpointSelectionError_nonneg (a b : ℝ) {coefficient : ℝ}
    (hc : 0 ≤ coefficient) : 0 ≤ endpointSelectionError a b coefficient := by
  unfold endpointSelectionError
  positivity

theorem endpointSelectionError_tendsto (a b : ℝ) {coefficient : ℕ → ℝ}
    (hc : Tendsto coefficient atTop (𝓝 0)) :
    Tendsto (fun n => endpointSelectionError a b (coefficient n)) atTop (𝓝 0) := by
  simpa only [endpointSelectionError, mul_zero] using hc.const_mul (8 * (|a| + |b| + 1))

theorem supportPenaltyLipschitz_stage_le (a b : ℝ) (level : ℕ) {coefficient : ℝ}
    (hc : 0 ≤ coefficient) :
    supportPenaltyLipschitz (|a| + |b| + 1) (normal (dyadic level))
      (fun i => coefficient * stageWeight level i) ≤ endpointSelectionError a b coefficient := by
  have hweights : (∑ i, coefficient * stageWeight level i) ≤ coefficient := by
    rw [← Finset.mul_sum]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (sum_stageWeight_le_one level) hc
  have hsum : (∑ i, coefficient * stageWeight level i *
      (|(normal (dyadic level) i).1| + |(normal (dyadic level) i).2|)) ≤ 2 * coefficient := by
    calc
      (∑ i, coefficient * stageWeight level i *
          (|(normal (dyadic level) i).1| + |(normal (dyadic level) i).2|)) ≤
          ∑ i, 2 * (coefficient * stageWeight level i) := by
        apply Finset.sum_le_sum
        intro i _
        have hn : |(normal (dyadic level) i).1| + |(normal (dyadic level) i).2| ≤ 2 := by
          rw [normal_eq_unitNormal]
          change |Real.cos _| + |Real.sin _| ≤ 2
          linarith [Real.abs_cos_le_one (fullAngle (dyadic level) i),
            Real.abs_sin_le_one (fullAngle (dyadic level) i)]
        have h := mul_le_mul_of_nonneg_left hn (mul_nonneg hc (stageWeight_nonneg level i))
        simpa only [mul_comm 2] using h
      _ = 2 * ∑ i, coefficient * stageWeight level i := by rw [Finset.mul_sum]
      _ ≤ 2 * coefficient := mul_le_mul_of_nonneg_left hweights (by norm_num)
  have h := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ 4 * (|a| + |b| + 1) by positivity)
  unfold supportPenaltyLipschitz endpointSelectionError
  nlinarith

theorem IsSelectedPolygon.maximizes_contained {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U)
    (V : Set Plane) (hV : IsDownwardCap V) (hVU : V ⊆ U) :
    finiteSpatialScore V (normal (dyadic level)) (pairList (dyadic level)) none -
      sampledPenalty V (normal (dyadic level)) (fun i => coefficient * stageWeight level i)
        (fun i => support target (normal (dyadic level) i)) ≤
    finiteSpatialScore U (normal (dyadic level)) (pairList (dyadic level)) none -
      sampledPenalty U (normal (dyadic level)) (fun i => coefficient * stageWeight level i)
        (fun i => support target (normal (dyadic level) i)) := by
  simpa only [score, stagePenalty, sampledPenalty_mul] using
    hU.maximizes V hV (hVU.trans hU.inBox)

theorem IsSelectedPolygon.right_erosion_bound {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U)
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hc : 0 ≤ coefficient) (hW : 1 ≤ capWidth U) :
    finiteRightMoment U (normal (dyadic level)) (pairList (dyadic level)) none ≤
      capRoof U (horizontalRight U) -
        rightEndpointPressure (capRoof U)
          (finiteBarrier U (normal (dyadic level)) (pairList (dyadic level)) none)
          (horizontalLeft U) (horizontalRight U) + endpointSelectionError a b coefficient := by
  have hpoints : ∀ p ∈ U, ∀ i,
      |coordDot p (normal (dyadic level) i)| ≤ |a| + |b| + 1 := by
    intro p hp i
    rw [normal_eq_unitNormal]
    exact abs_coordDot_unitNormal_le_box (hU.inBox hp) _
  have htargets : ∀ i, |support target (normal (dyadic level) i)| ≤ |a| + |b| + 1 := by
    intro i
    apply abs_support_le_of_pointwise_bound hTarget
    intro p hp
    rw [normal_eq_unitNormal]
    exact abs_coordDot_unitNormal_le_box (hTargetBox hp) _
  have h := selected_right_erosion_moment hU.isCap hW (normal (dyadic level))
    (normal_snd_pos (dyadic level)) (wallSlopes_injective (dyadic level)) hU.polygon_eq
    (pairList (dyadic level)) none (normal (dyadic level))
    (fun i => coefficient * stageWeight level i)
    (fun i => support target (normal (dyadic level) i))
    (show 0 ≤ |a| + |b| + 1 by positivity)
    (fun i => mul_nonneg hc (stageWeight_nonneg level i)) hpoints htargets hU.maximizes_contained
  exact h.trans (add_le_add_left (supportPenaltyLipschitz_stage_le a b level hc) _)

theorem IsSelectedPolygon.left_erosion_bound {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U)
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hc : 0 ≤ coefficient) (hW : 1 ≤ capWidth U) :
    finiteLeftMoment U (normal (dyadic level)) (pairList (dyadic level)) none ≤
      capRoof U (horizontalLeft U) -
        leftEndpointPressure (capRoof U)
          (finiteBarrier U (normal (dyadic level)) (pairList (dyadic level)) none)
          (horizontalLeft U) (horizontalRight U) + endpointSelectionError a b coefficient := by
  have hpoints : ∀ p ∈ U, ∀ i,
      |coordDot p (normal (dyadic level) i)| ≤ |a| + |b| + 1 := by
    intro p hp i
    rw [normal_eq_unitNormal]
    exact abs_coordDot_unitNormal_le_box (hU.inBox hp) _
  have htargets : ∀ i, |support target (normal (dyadic level) i)| ≤ |a| + |b| + 1 := by
    intro i
    apply abs_support_le_of_pointwise_bound hTarget
    intro p hp
    rw [normal_eq_unitNormal]
    exact abs_coordDot_unitNormal_le_box (hTargetBox hp) _
  have h := selected_left_erosion_moment hU.isCap hW (normal (dyadic level))
    (normal_snd_pos (dyadic level)) (wallSlopes_injective (dyadic level)) hU.polygon_eq
    (pairList (dyadic level)) none (normal (dyadic level))
    (fun i => coefficient * stageWeight level i)
    (fun i => support target (normal (dyadic level) i))
    (show 0 ≤ |a| + |b| + 1 by positivity)
    (fun i => mul_nonneg hc (stageWeight_nonneg level i)) hpoints htargets hU.maximizes_contained
  exact h.trans (add_le_add_left (supportPenaltyLipschitz_stage_le a b level hc) _)

theorem IsSelectedPolygon.right_inward_pressure_bound {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U)
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hc : 0 ≤ coefficient) (hW : 1 ≤ capWidth U) :
    rightEndpointPressure (capRoof U)
      (finiteBarrier U (normal (dyadic level)) (pairList (dyadic level)) none)
      (horizontalLeft U) (horizontalRight U) ≤
        capRoof U (horizontalRight U) + endpointSelectionError a b coefficient := by
  have hpoints : ∀ p ∈ U, ∀ i,
      |coordDot p (normal (dyadic level) i)| ≤ |a| + |b| + 1 := by
    intro p hp i
    rw [normal_eq_unitNormal]
    exact abs_coordDot_unitNormal_le_box (hU.inBox hp) _
  have htargets : ∀ i, |support target (normal (dyadic level) i)| ≤ |a| + |b| + 1 := by
    intro i
    apply abs_support_le_of_pointwise_bound hTarget
    intro p hp
    rw [normal_eq_unitNormal]
    exact abs_coordDot_unitNormal_le_box (hTargetBox hp) _
  have h := selected_right_inward_pressure hU.isCap hW (normal (dyadic level))
    (fun i => (normal_snd_pos (dyadic level) i).le) (pairList (dyadic level)) none
    (normal (dyadic level)) (fun i => coefficient * stageWeight level i)
    (fun i => support target (normal (dyadic level) i))
    (show 0 ≤ |a| + |b| + 1 by positivity)
    (fun i => mul_nonneg hc (stageWeight_nonneg level i)) hpoints htargets hU.maximizes_contained
  exact h.trans (add_le_add_left (supportPenaltyLipschitz_stage_le a b level hc) _)

theorem IsSelectedPolygon.left_inward_pressure_bound {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U)
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hc : 0 ≤ coefficient) (hW : 1 ≤ capWidth U) :
    leftEndpointPressure (capRoof U)
      (finiteBarrier U (normal (dyadic level)) (pairList (dyadic level)) none)
      (horizontalLeft U) (horizontalRight U) ≤
        capRoof U (horizontalLeft U) + endpointSelectionError a b coefficient := by
  have hpoints : ∀ p ∈ U, ∀ i,
      |coordDot p (normal (dyadic level) i)| ≤ |a| + |b| + 1 := by
    intro p hp i
    rw [normal_eq_unitNormal]
    exact abs_coordDot_unitNormal_le_box (hU.inBox hp) _
  have htargets : ∀ i, |support target (normal (dyadic level) i)| ≤ |a| + |b| + 1 := by
    intro i
    apply abs_support_le_of_pointwise_bound hTarget
    intro p hp
    rw [normal_eq_unitNormal]
    exact abs_coordDot_unitNormal_le_box (hTargetBox hp) _
  have h := selected_left_inward_pressure hU.isCap hW (normal (dyadic level))
    (fun i => (normal_snd_pos (dyadic level) i).le) (pairList (dyadic level)) none
    (normal (dyadic level)) (fun i => coefficient * stageWeight level i)
    (fun i => support target (normal (dyadic level) i))
    (show 0 ≤ |a| + |b| + 1 by positivity)
    (fun i => mul_nonneg hc (stageWeight_nonneg level i)) hpoints htargets hU.maximizes_contained
  exact h.trans (add_le_add_left (supportPenaltyLipschitz_stage_le a b level hc) _)

/-- A positive right end face has an actual outward competitor. The
strict box slack is used only to keep this small competitor in the box. -/
theorem IsSelectedPolygon.right_height_le_pressure_of_pos {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U)
    (hslack : horizontalRight U < b) (he : 0 < capRoof U (horizontalRight U)) :
    capRoof U (horizontalRight U) ≤
      rightEndpointPressure (capRoof U)
        (finiteBarrier U (normal (dyadic level)) (pairList (dyadic level)) none)
        (horizontalLeft U) (horizontalRight U) := by
  let grid := dyadic level
  let height : SourceIndex grid → ℝ := fun i => support U (normal grid i)
  let F : ℝ → ℝ := fun ε => intervalSpatialScore (roofEnvelope (normal grid) height)
    (barrierEnvelope (normal grid) height (pairList grid) none)
    (horizontalLeft U) (horizontalRight U + ε)
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  have hroof := eqOn_roofEnvelope_of_circumscription hU.isCap (normal grid)
    (normal_snd_pos grid) hU.polygon_eq
  have hbarrier : barrierEnvelope (normal grid) height (pairList grid) none =
      finiteBarrier U (normal grid) (pairList grid) none := by
    funext x
    exact (finiteBarrier_eq_eval (normal grid) height (fun _ => rfl) (pairList grid) none x).symm
  have hzero : F 0 = score U grid := by
    dsimp only [F]
    rw [add_zero, hbarrier]
    exact intervalSpatialScore_congr_roof hlr hroof
  have hface := subset_circumscription hU.isCap (normal grid)
    (capRoof_mem hU.isCap.isCompact (horizontalRight_mem hU.isCap.nonempty hU.isCap.isCompact))
  obtain ⟨δ, hδ, hfamily⟩ := exists_right_axis_variation (normal grid) height hlr
    (normal_snd_pos grid) (circumscription_baseline hU.isCap (normal grid))
    (support_circumscription hU.isCap (normal grid)) hface he
  have hleftBox : a ≤ horizontalLeft U :=
    (hU.inBox (hU.isCap.baseline_mem_of_mem_projection
      (horizontalLeft_mem hU.isCap.nonempty hU.isCap.isCompact))).1.1
  have hmax : ∀ᶠ ε in 𝓝[>] (0 : ℝ), F ε ≤ F 0 := by
    have hsmall : Iio δ ∈ 𝓝[>] (0 : ℝ) := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)
    have hboxSmall : Iio (b - horizontalRight U) ∈ 𝓝[>] (0 : ℝ) :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (sub_pos.mpr hslack))
    filter_upwards [hsmall, hboxSmall, self_mem_nhdsWithin] with ε hεδ hεbox hεpos
    have hε0 : 0 ≤ ε := (show 0 < ε from hεpos).le
    obtain ⟨hV, hbase, _, hsupport⟩ := hfamily ε ⟨hε0, hεδ⟩
    let V := upperPolygon (horizontalLeft U) (horizontalRight U + ε) (normal grid) height
    have hVB : V ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 := by
      intro p hp
      obtain ⟨hx, hy, _⟩ := (mem_upperPolygon_iff _ _ _ _ _).mp hp
      exact ⟨⟨hleftBox.trans hx.1, by linarith [hx.2]⟩, hy⟩
    have hpenalty : stagePenalty level target V = stagePenalty level target U := by
      unfold stagePenalty sampledPenalty heightPenalty
      apply Finset.sum_congr rfl
      intro i _
      rw [hsupport i]
    have hscore : score V grid = F ε := by
      simpa only [score, V, F, barrierEnvelope] using
        finiteSpatialScore_upperPolygon (normal grid) height (by linarith)
          (normal_snd_pos grid) hbase hsupport (pairList grid) none
    have h := hU.maximizes V hV hVB
    rw [hpenalty, hscore, ← hzero] at h
    linarith
  have hderiv := hasDerivAt_intervalSpatialScore_right
    (continuous_roofEnvelope (normal grid) height)
    (continuous_barrierEnvelope (normal grid) height (pairList grid) none)
    (horizontalLeft U) (horizontalRight U)
  have hsign := hasDerivAt_nonpos_of_right_max (f := F) hderiv hmax
  have hpressure : roofEnvelope (normal grid) height (horizontalRight U) ≤
      rightEndpointPressure (roofEnvelope (normal grid) height)
        (barrierEnvelope (normal grid) height (pairList grid) none)
        (horizontalLeft U) (horizontalRight U) := by
    unfold rightEndpointPressure
    linarith
  rw [hbarrier, rightEndpointPressure_congr_roof hlr hroof, hroof ⟨hlr, le_rfl⟩] at hpressure
  exact hpressure

theorem IsSelectedPolygon.left_height_le_pressure_of_pos {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U)
    (hslack : a < horizontalLeft U) (he : 0 < capRoof U (horizontalLeft U)) :
    capRoof U (horizontalLeft U) ≤
      leftEndpointPressure (capRoof U)
        (finiteBarrier U (normal (dyadic level)) (pairList (dyadic level)) none)
        (horizontalLeft U) (horizontalRight U) := by
  let grid := dyadic level
  let height : SourceIndex grid → ℝ := fun i => support U (normal grid i)
  let F : ℝ → ℝ := fun ε => intervalSpatialScore (roofEnvelope (normal grid) height)
    (barrierEnvelope (normal grid) height (pairList grid) none)
    (horizontalLeft U - ε) (horizontalRight U)
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  have hroof := eqOn_roofEnvelope_of_circumscription hU.isCap (normal grid)
    (normal_snd_pos grid) hU.polygon_eq
  have hbarrier : barrierEnvelope (normal grid) height (pairList grid) none =
      finiteBarrier U (normal grid) (pairList grid) none := by
    funext x
    exact (finiteBarrier_eq_eval (normal grid) height (fun _ => rfl) (pairList grid) none x).symm
  have hzero : F 0 = score U grid := by
    dsimp only [F]
    rw [sub_zero, hbarrier]
    exact intervalSpatialScore_congr_roof hlr hroof
  have hface := subset_circumscription hU.isCap (normal grid)
    (capRoof_mem hU.isCap.isCompact (horizontalLeft_mem hU.isCap.nonempty hU.isCap.isCompact))
  obtain ⟨δ, hδ, hfamily⟩ := exists_left_axis_variation (normal grid) height hlr
    (normal_snd_pos grid) (circumscription_baseline hU.isCap (normal grid))
    (support_circumscription hU.isCap (normal grid)) hface he
  have hrightBox : horizontalRight U ≤ b :=
    (hU.inBox (hU.isCap.baseline_mem_of_mem_projection
      (horizontalRight_mem hU.isCap.nonempty hU.isCap.isCompact))).1.2
  have hmax : ∀ᶠ ε in 𝓝[>] (0 : ℝ), F ε ≤ F 0 := by
    have hsmall : Iio δ ∈ 𝓝[>] (0 : ℝ) := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)
    have hboxSmall : Iio (horizontalLeft U - a) ∈ 𝓝[>] (0 : ℝ) :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (sub_pos.mpr hslack))
    filter_upwards [hsmall, hboxSmall, self_mem_nhdsWithin] with ε hεδ hεbox hεpos
    have hε0 : 0 ≤ ε := (show 0 < ε from hεpos).le
    obtain ⟨hV, hbase, _, hsupport⟩ := hfamily ε ⟨hε0, hεδ⟩
    let V := upperPolygon (horizontalLeft U - ε) (horizontalRight U) (normal grid) height
    have hVB : V ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 := by
      intro p hp
      obtain ⟨hx, hy, _⟩ := (mem_upperPolygon_iff _ _ _ _ _).mp hp
      exact ⟨⟨by linarith [hx.1], hx.2.trans hrightBox⟩, hy⟩
    have hpenalty : stagePenalty level target V = stagePenalty level target U := by
      unfold stagePenalty sampledPenalty heightPenalty
      apply Finset.sum_congr rfl
      intro i _
      rw [hsupport i]
    have hscore : score V grid = F ε := by
      simpa only [score, V, F, barrierEnvelope] using
        finiteSpatialScore_upperPolygon (normal grid) height (by linarith)
          (normal_snd_pos grid) hbase hsupport (pairList grid) none
    have h := hU.maximizes V hV hVB
    rw [hpenalty, hscore, ← hzero] at h
    linarith
  have hderiv := hasDerivAt_intervalSpatialScore_left
    (continuous_roofEnvelope (normal grid) height)
    (continuous_barrierEnvelope (normal grid) height (pairList grid) none)
    (horizontalLeft U) (horizontalRight U)
  have hsign := hasDerivAt_nonpos_of_right_max (f := F) hderiv hmax
  have hpressure : roofEnvelope (normal grid) height (horizontalLeft U) ≤
      leftEndpointPressure (roofEnvelope (normal grid) height)
        (barrierEnvelope (normal grid) height (pairList grid) none)
        (horizontalLeft U) (horizontalRight U) := by
    unfold leftEndpointPressure
    linarith
  rw [hbarrier, leftEndpointPressure_congr_roof hlr hroof, hroof ⟨le_rfl, hlr⟩] at hpressure
  exact hpressure

theorem IsSelectedPolygon.right_height_le_positive_pressure {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hslack : horizontalRight U < b) :
    capRoof U (horizontalRight U) ≤
      max (rightEndpointPressure (capRoof U)
        (finiteBarrier U (normal (dyadic level)) (pairList (dyadic level)) none)
        (horizontalLeft U) (horizontalRight U)) 0 := by
  by_cases he : 0 < capRoof U (horizontalRight U)
  · exact (hU.right_height_le_pressure_of_pos hslack he).trans (le_max_left _ _)
  · exact (le_of_not_gt he).trans (le_max_right _ _)

theorem IsSelectedPolygon.left_height_le_positive_pressure {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hslack : a < horizontalLeft U) :
    capRoof U (horizontalLeft U) ≤
      max (leftEndpointPressure (capRoof U)
        (finiteBarrier U (normal (dyadic level)) (pairList (dyadic level)) none)
        (horizontalLeft U) (horizontalRight U)) 0 := by
  by_cases he : 0 < capRoof U (horizontalLeft U)
  · exact (hU.left_height_le_pressure_of_pos hslack he).trans (le_max_left _ _)
  · exact (le_of_not_gt he).trans (le_max_right _ _)

/-- Finite approximate complementarity, including zero end heights. -/
theorem IsSelectedPolygon.abs_right_complementarity_le {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U)
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hc : 0 ≤ coefficient) (hW : 1 ≤ capWidth U) (hslack : horizontalRight U < b) :
    |capRoof U (horizontalRight U) -
      max (rightEndpointPressure (capRoof U)
        (finiteBarrier U (normal (dyadic level)) (pairList (dyadic level)) none)
        (horizontalLeft U) (horizontalRight U)) 0| ≤ endpointSelectionError a b coefficient := by
  have hupper := hU.right_height_le_positive_pressure hslack
  have hlower := hU.right_inward_pressure_bound hTarget hTargetBox hc hW
  have he0 := capRoof_nonneg hU.isCap.isCompact (fun p hp => (hU.isCap.inStrip hp).1)
    (horizontalRight U)
  have hK0 := endpointSelectionError_nonneg a b hc
  have hmax := max_le hlower (add_nonneg he0 hK0)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem IsSelectedPolygon.abs_left_complementarity_le {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U)
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hc : 0 ≤ coefficient) (hW : 1 ≤ capWidth U) (hslack : a < horizontalLeft U) :
    |capRoof U (horizontalLeft U) -
      max (leftEndpointPressure (capRoof U)
        (finiteBarrier U (normal (dyadic level)) (pairList (dyadic level)) none)
        (horizontalLeft U) (horizontalRight U)) 0| ≤ endpointSelectionError a b coefficient := by
  have hupper := hU.left_height_le_positive_pressure hslack
  have hlower := hU.left_inward_pressure_bound hTarget hTargetBox hc hW
  have he0 := capRoof_nonneg hU.isCap.isCompact (fun p hp => (hU.isCap.inStrip hp).1)
    (horizontalLeft U)
  have hK0 := endpointSelectionError_nonneg a b hc
  have hmax := max_le hlower (add_nonneg he0 hK0)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end AngularGrid

end AmbidextrousSofa
