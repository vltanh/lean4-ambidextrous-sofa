module

public import AmbidextrousSofa.Analysis.SelectedEndpointMoments
public import AmbidextrousSofa.Analysis.PartialSelectedCurvature

@[expose] public section

/-!
# Endpoint variation for actual proper-angle selected polygons

The physical finite source system retains every visited corner and the
whole terminal first wall. Inward and outward endpoint variations use
that same system. Aggregated support weights preserve the original
selection penalty, and its uniform endpoint error vanishes with the
selection coefficient.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa
namespace PartialGrid

open FinitePolygon AngularGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

theorem supportPenaltyLipschitz_stage_le (a b : ℝ) (level : ℕ) {coefficient : ℝ}
    (hc : 0 ≤ coefficient) :
    supportPenaltyLipschitz (|a| + |b| + 1) (normal α (dyadic level))
      (fun i => coefficient * stageWeight α level i) ≤ endpointSelectionError a b coefficient := by
  have hsum : (∑ i, coefficient * stageWeight α level i *
      (|(normal α (dyadic level) i).1| + |(normal α (dyadic level) i).2|)) ≤ 2 * coefficient :=
    calc _ ≤ ∑ i, coefficient * stageWeight α level i * 2 := Finset.sum_le_sum fun i _ => by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hc (stageWeight_nonneg α level i))
          rw [normal_eq_unitNormal]
          exact (add_le_add (Real.abs_cos_le_one _) (Real.abs_sin_le_one _)).trans_eq
            one_add_one_eq_two
      _ = 2 * (coefficient * ∑ i, stageWeight α level i) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
      _ ≤ 2 * coefficient := by
          linarith [mul_le_of_le_one_right hc (sum_stageWeight_le_one α level)]
  unfold supportPenaltyLipschitz endpointSelectionError
  linarith [mul_le_mul_of_nonneg_left hsum (show 0 ≤ 4 * (|a| + |b| + 1) by positivity)]

theorem IsSelectedPolygon.maximizes_contained {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U)
    (V : Set Plane) (hV : IsDownwardCap V) (hVU : V ⊆ U) :
    finiteSpatialScore V (normal α (dyadic level)) (pairList α (dyadic level)) (some (terminalIndex α hαL (dyadic level))) -
      sampledPenalty V (normal α (dyadic level)) (fun i => coefficient * stageWeight α level i)
        (fun i => support target (normal α (dyadic level) i)) ≤
    finiteSpatialScore U (normal α (dyadic level)) (pairList α (dyadic level)) (some (terminalIndex α hαL (dyadic level))) -
      sampledPenalty U (normal α (dyadic level)) (fun i => coefficient * stageWeight α level i)
        (fun i => support target (normal α (dyadic level) i)) := by
  simpa only [score, sampledPenalty_mul, sampledPenalty_eq_stagePenalty] using
    hU.maximizes V hV (hVU.trans hU.inBox)

/-- The box bounds the selected points and the target supports in every grid direction. -/
private theorem IsSelectedPolygon.support_bounds {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U)
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1) :
    (∀ p ∈ U, ∀ i, |coordDot p (normal α (dyadic level) i)| ≤ |a| + |b| + 1) ∧
      ∀ i, |support target (normal α (dyadic level) i)| ≤ |a| + |b| + 1 := by
  have h (p : Plane) (hp : p ∈ Icc a b ×ˢ Icc (0 : ℝ) 1) (i : SourceIndex α (dyadic level)) :
      |coordDot p (normal α (dyadic level) i)| ≤ |a| + |b| + 1 := by
    rw [normal_eq_unitNormal]; exact abs_coordDot_unitNormal_le_box hp _
  exact ⟨fun p hp => h p (hU.inBox hp),
    fun i => abs_support_le_of_pointwise_bound hTarget _ fun p hp => h p (hTargetBox hp) i⟩

theorem IsSelectedPolygon.right_erosion_bound {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U)
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hc : 0 ≤ coefficient) (hW : 1 ≤ capWidth U) :
    finiteRightMoment U (normal α (dyadic level)) (pairList α (dyadic level)) (some (terminalIndex α hαL (dyadic level))) ≤
      capRoof U (horizontalRight U) -
        rightEndpointPressure (capRoof U)
          (finiteBarrier U (normal α (dyadic level)) (pairList α (dyadic level)) (some (terminalIndex α hαL (dyadic level))))
          (horizontalLeft U) (horizontalRight U) + endpointSelectionError a b coefficient := by
  obtain ⟨hpoints, htargets⟩ := hU.support_bounds hTarget hTargetBox
  exact (selected_right_erosion_moment hU.isCap hW _ (normal_snd_pos _ _)
    (wallSlopes_injective _ _) hU.polygon_eq _ _ _ _ _ (by positivity)
    (fun i => mul_nonneg hc (stageWeight_nonneg α level i)) hpoints htargets
    hU.maximizes_contained).trans (add_le_add_right (supportPenaltyLipschitz_stage_le a b level hc) _)

theorem IsSelectedPolygon.left_erosion_bound {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U)
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hc : 0 ≤ coefficient) (hW : 1 ≤ capWidth U) :
    finiteLeftMoment U (normal α (dyadic level)) (pairList α (dyadic level)) (some (terminalIndex α hαL (dyadic level))) ≤
      capRoof U (horizontalLeft U) -
        leftEndpointPressure (capRoof U)
          (finiteBarrier U (normal α (dyadic level)) (pairList α (dyadic level)) (some (terminalIndex α hαL (dyadic level))))
          (horizontalLeft U) (horizontalRight U) + endpointSelectionError a b coefficient := by
  obtain ⟨hpoints, htargets⟩ := hU.support_bounds hTarget hTargetBox
  exact (selected_left_erosion_moment hU.isCap hW _ (normal_snd_pos _ _)
    (wallSlopes_injective _ _) hU.polygon_eq _ _ _ _ _ (by positivity)
    (fun i => mul_nonneg hc (stageWeight_nonneg α level i)) hpoints htargets
    hU.maximizes_contained).trans (add_le_add_right (supportPenaltyLipschitz_stage_le a b level hc) _)

theorem IsSelectedPolygon.right_inward_pressure_bound {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U)
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hc : 0 ≤ coefficient) (hW : 1 ≤ capWidth U) :
    rightEndpointPressure (capRoof U)
      (finiteBarrier U (normal α (dyadic level)) (pairList α (dyadic level)) (some (terminalIndex α hαL (dyadic level))))
      (horizontalLeft U) (horizontalRight U) ≤
        capRoof U (horizontalRight U) + endpointSelectionError a b coefficient := by
  obtain ⟨hpoints, htargets⟩ := hU.support_bounds hTarget hTargetBox
  exact (selected_right_inward_pressure hU.isCap hW _
    (fun i => (normal_snd_pos _ _ i).le) _ _ _ _ _ (by positivity)
    (fun i => mul_nonneg hc (stageWeight_nonneg α level i)) hpoints htargets
    hU.maximizes_contained).trans (add_le_add_right (supportPenaltyLipschitz_stage_le a b level hc) _)

theorem IsSelectedPolygon.left_inward_pressure_bound {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U)
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hc : 0 ≤ coefficient) (hW : 1 ≤ capWidth U) :
    leftEndpointPressure (capRoof U)
      (finiteBarrier U (normal α (dyadic level)) (pairList α (dyadic level)) (some (terminalIndex α hαL (dyadic level))))
      (horizontalLeft U) (horizontalRight U) ≤
        capRoof U (horizontalLeft U) + endpointSelectionError a b coefficient := by
  obtain ⟨hpoints, htargets⟩ := hU.support_bounds hTarget hTargetBox
  exact (selected_left_inward_pressure hU.isCap hW _
    (fun i => (normal_snd_pos _ _ i).le) _ _ _ _ _ (by positivity)
    (fun i => mul_nonneg hc (stageWeight_nonneg α level i)) hpoints htargets
    hU.maximizes_contained).trans (add_le_add_right (supportPenaltyLipschitz_stage_le a b level hc) _)

/-- A positive right end face has an actual outward competitor. The
strict box slack is used only to keep this small competitor in the box. -/
theorem IsSelectedPolygon.right_height_le_pressure_of_pos {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U)
    (hslack : horizontalRight U < b) (he : 0 < capRoof U (horizontalRight U)) :
    capRoof U (horizontalRight U) ≤
      rightEndpointPressure (capRoof U)
        (finiteBarrier U (normal α (dyadic level)) (pairList α (dyadic level)) (some (terminalIndex α hαL (dyadic level))))
        (horizontalLeft U) (horizontalRight U) := by
  let grid := dyadic level
  let height : SourceIndex α grid → ℝ := fun i => support U (normal α grid i)
  let F : ℝ → ℝ := fun ε => intervalSpatialScore (roofEnvelope (normal α grid) height)
    (barrierEnvelope (normal α grid) height (pairList α grid) (some (terminalIndex α hαL grid)))
    (horizontalLeft U) (horizontalRight U + ε)
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  have hroof := eqOn_roofEnvelope_of_circumscription hU.isCap (normal α grid)
    (normal_snd_pos α grid) hU.polygon_eq
  have hbarrier : barrierEnvelope (normal α grid) height (pairList α grid)
      (some (terminalIndex α hαL grid)) =
      finiteBarrier U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)) :=
    funext fun x => (finiteBarrier_eq_eval _ height (fun _ => rfl) _ _ x).symm
  have hzero : F 0 = score U α hαL grid := by
    simp only [F, add_zero, hbarrier]; exact intervalSpatialScore_congr_roof hlr hroof
  obtain ⟨δ, hδ, hfamily⟩ := exists_right_axis_variation (normal α grid) height hlr
    (normal_snd_pos α grid) (circumscription_baseline hU.isCap (normal α grid))
    (support_circumscription hU.isCap (normal α grid)) (subset_circumscription hU.isCap _
      (capRoof_mem hU.isCap.isCompact (horizontalRight_mem hU.isCap.nonempty hU.isCap.isCompact))) he
  have hleftBox : a ≤ horizontalLeft U := (hU.inBox (hU.isCap.baseline_mem_of_mem_projection
    (horizontalLeft_mem hU.isCap.nonempty hU.isCap.isCompact))).1.1
  have hmax : ∀ᶠ ε in 𝓝[>] (0 : ℝ), F ε ≤ F 0 := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min hδ (sub_pos.mpr hslack))] with ε ⟨hε0, hε⟩
    obtain ⟨hV, hbase, _, hsupport⟩ := hfamily ε ⟨hε0.le, hε.trans_le (min_le_left _ _)⟩
    have hscore : score (upperPolygon _ _ (normal α grid) height) α hαL grid = F ε :=
      finiteSpatialScore_upperPolygon _ height (by linarith) (normal_snd_pos α grid) hbase
        hsupport _ _
    have h := hU.maximizes _ hV fun p hp => by
      obtain ⟨hx, hy, _⟩ := (mem_upperPolygon_iff _ _ _ _ _).mp hp
      exact ⟨⟨hleftBox.trans hx.1, by linarith [hx.2, hε.trans_le (min_le_right _ _)]⟩, hy⟩
    have hpen : stagePenalty level target (upperPolygon (horizontalLeft U) (horizontalRight U + ε)
        (normal α grid) height) = stagePenalty level target U := by
      rw [← sampledPenalty_eq_stagePenalty α, ← sampledPenalty_eq_stagePenalty α]
      unfold sampledPenalty heightPenalty
      exact Finset.sum_congr rfl fun i _ => by beta_reduce; rw [hsupport i]
    rw [hpen, hscore, ← hzero] at h
    linarith
  have hsign := hasDerivAt_nonpos_of_right_max (f := F) (hasDerivAt_intervalSpatialScore_right
    (continuous_roofEnvelope (normal α grid) height)
    (continuous_barrierEnvelope (normal α grid) height (pairList α grid) _) _ _) hmax
  rw [← hbarrier, ← rightEndpointPressure_congr_roof hlr hroof, ← hroof ⟨hlr, le_rfl⟩]
  unfold rightEndpointPressure
  linarith

theorem IsSelectedPolygon.left_height_le_pressure_of_pos {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U)
    (hslack : a < horizontalLeft U) (he : 0 < capRoof U (horizontalLeft U)) :
    capRoof U (horizontalLeft U) ≤
      leftEndpointPressure (capRoof U)
        (finiteBarrier U (normal α (dyadic level)) (pairList α (dyadic level)) (some (terminalIndex α hαL (dyadic level))))
        (horizontalLeft U) (horizontalRight U) := by
  let grid := dyadic level
  let height : SourceIndex α grid → ℝ := fun i => support U (normal α grid i)
  let F : ℝ → ℝ := fun ε => intervalSpatialScore (roofEnvelope (normal α grid) height)
    (barrierEnvelope (normal α grid) height (pairList α grid) (some (terminalIndex α hαL grid)))
    (horizontalLeft U - ε) (horizontalRight U)
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  have hroof := eqOn_roofEnvelope_of_circumscription hU.isCap (normal α grid)
    (normal_snd_pos α grid) hU.polygon_eq
  have hbarrier : barrierEnvelope (normal α grid) height (pairList α grid)
      (some (terminalIndex α hαL grid)) =
      finiteBarrier U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)) :=
    funext fun x => (finiteBarrier_eq_eval _ height (fun _ => rfl) _ _ x).symm
  have hzero : F 0 = score U α hαL grid := by
    simp only [F, sub_zero, hbarrier]; exact intervalSpatialScore_congr_roof hlr hroof
  obtain ⟨δ, hδ, hfamily⟩ := exists_left_axis_variation (normal α grid) height hlr
    (normal_snd_pos α grid) (circumscription_baseline hU.isCap (normal α grid))
    (support_circumscription hU.isCap (normal α grid)) (subset_circumscription hU.isCap _
      (capRoof_mem hU.isCap.isCompact (horizontalLeft_mem hU.isCap.nonempty hU.isCap.isCompact))) he
  have hrightBox : horizontalRight U ≤ b := (hU.inBox (hU.isCap.baseline_mem_of_mem_projection
    (horizontalRight_mem hU.isCap.nonempty hU.isCap.isCompact))).1.2
  have hmax : ∀ᶠ ε in 𝓝[>] (0 : ℝ), F ε ≤ F 0 := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min hδ (sub_pos.mpr hslack))] with ε ⟨hε0, hε⟩
    obtain ⟨hV, hbase, _, hsupport⟩ := hfamily ε ⟨hε0.le, hε.trans_le (min_le_left _ _)⟩
    have hscore : score (upperPolygon _ _ (normal α grid) height) α hαL grid = F ε :=
      finiteSpatialScore_upperPolygon _ height (by linarith) (normal_snd_pos α grid) hbase
        hsupport _ _
    have h := hU.maximizes _ hV fun p hp => by
      obtain ⟨hx, hy, _⟩ := (mem_upperPolygon_iff _ _ _ _ _).mp hp
      exact ⟨⟨by linarith [hx.1, hε.trans_le (min_le_right _ _)], hx.2.trans hrightBox⟩, hy⟩
    have hpen : stagePenalty level target (upperPolygon (horizontalLeft U - ε) (horizontalRight U)
        (normal α grid) height) = stagePenalty level target U := by
      rw [← sampledPenalty_eq_stagePenalty α, ← sampledPenalty_eq_stagePenalty α]
      unfold sampledPenalty heightPenalty
      exact Finset.sum_congr rfl fun i _ => by beta_reduce; rw [hsupport i]
    rw [hpen, hscore, ← hzero] at h
    linarith
  have hsign := hasDerivAt_nonpos_of_right_max (f := F) (hasDerivAt_intervalSpatialScore_left
    (continuous_roofEnvelope (normal α grid) height)
    (continuous_barrierEnvelope (normal α grid) height (pairList α grid) _) _ _) hmax
  rw [← hbarrier, ← leftEndpointPressure_congr_roof hlr hroof, ← hroof ⟨le_rfl, hlr⟩]
  unfold leftEndpointPressure
  linarith

theorem IsSelectedPolygon.right_height_le_positive_pressure {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U) (hslack : horizontalRight U < b) :
    capRoof U (horizontalRight U) ≤
      max (rightEndpointPressure (capRoof U)
        (finiteBarrier U (normal α (dyadic level)) (pairList α (dyadic level)) (some (terminalIndex α hαL (dyadic level))))
        (horizontalLeft U) (horizontalRight U)) 0 := by
  by_cases he : 0 < capRoof U (horizontalRight U)
  · exact (hU.right_height_le_pressure_of_pos hslack he).trans (le_max_left _ _)
  · exact (le_of_not_gt he).trans (le_max_right _ _)

theorem IsSelectedPolygon.left_height_le_positive_pressure {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U) (hslack : a < horizontalLeft U) :
    capRoof U (horizontalLeft U) ≤
      max (leftEndpointPressure (capRoof U)
        (finiteBarrier U (normal α (dyadic level)) (pairList α (dyadic level)) (some (terminalIndex α hαL (dyadic level))))
        (horizontalLeft U) (horizontalRight U)) 0 := by
  by_cases he : 0 < capRoof U (horizontalLeft U)
  · exact (hU.left_height_le_pressure_of_pos hslack he).trans (le_max_left _ _)
  · exact (le_of_not_gt he).trans (le_max_right _ _)

/-- Finite approximate complementarity, including zero end heights. -/
theorem IsSelectedPolygon.abs_right_complementarity_le {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U)
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hc : 0 ≤ coefficient) (hW : 1 ≤ capWidth U) (hslack : horizontalRight U < b) :
    |capRoof U (horizontalRight U) -
      max (rightEndpointPressure (capRoof U)
        (finiteBarrier U (normal α (dyadic level)) (pairList α (dyadic level)) (some (terminalIndex α hαL (dyadic level))))
        (horizontalLeft U) (horizontalRight U)) 0| ≤ endpointSelectionError a b coefficient := by
  have hK0 := endpointSelectionError_nonneg a b hc
  have hmax := max_le (hU.right_inward_pressure_bound hTarget hTargetBox hc hW)
    (add_nonneg (capRoof_nonneg hU.isCap.isCompact (fun p hp => (hU.isCap.inStrip hp).1) _) hK0)
  exact abs_le.mpr ⟨by linarith, by linarith [hU.right_height_le_positive_pressure hslack]⟩

theorem IsSelectedPolygon.abs_left_complementarity_le {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U)
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hc : 0 ≤ coefficient) (hW : 1 ≤ capWidth U) (hslack : a < horizontalLeft U) :
    |capRoof U (horizontalLeft U) -
      max (leftEndpointPressure (capRoof U)
        (finiteBarrier U (normal α (dyadic level)) (pairList α (dyadic level)) (some (terminalIndex α hαL (dyadic level))))
        (horizontalLeft U) (horizontalRight U)) 0| ≤ endpointSelectionError a b coefficient := by
  have hK0 := endpointSelectionError_nonneg a b hc
  have hmax := max_le (hU.left_inward_pressure_bound hTarget hTargetBox hc hW)
    (add_nonneg (capRoof_nonneg hU.isCap.isCompact (fun p hp => (hU.isCap.inStrip hp).1) _) hK0)
  exact abs_le.mpr ⟨by linarith, by linarith [hU.left_height_le_positive_pressure hslack]⟩

end PartialGrid
end AmbidextrousSofa
