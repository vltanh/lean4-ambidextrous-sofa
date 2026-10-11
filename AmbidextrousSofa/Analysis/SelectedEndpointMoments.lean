module

public import AmbidextrousSofa.Analysis.ErosionMoments
public import AmbidextrousSofa.Analysis.SelectedCurvature

@[expose] public section

/-!
# Endpoint estimates for selected polygons

A selected polygon of finitely many unit normals is a boxed cap, equal to its own
circumscription, that maximizes the finite spatial score minus a support penalty whose weights
total at most a coefficient. The abstract finite variation theorems give its endpoint estimates,
with an explicit error tending to zero with the coefficient. Positive end faces allow an actual
outward variation inside the box; zero end faces are handled by a positive part. The dyadic
selected polygons of the full turn are selected polygons in this sense.
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
  have hy : |p.2| ≤ 1 := abs_le.mpr ⟨by linarith [hp.2.1], hp.2.2⟩
  calc |coordDot p (unitNormal t)| ≤ |p.1| * |Real.cos t| + |p.2| * |Real.sin t| := by
        simpa only [coordDot, unitNormal, abs_mul] using
          abs_add_le (p.1 * Real.cos t) (p.2 * Real.sin t)
    _ ≤ |a| + |b| + 1 := by
        linarith [mul_le_mul_of_nonneg_left (Real.abs_cos_le_one t) (abs_nonneg p.1),
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one t) (abs_nonneg p.2)]

namespace FinitePolygon

def endpointSelectionError (a b c : ℝ) : ℝ :=
  8 * (|a| + |b| + 1) * c

theorem endpointSelectionError_nonneg (a b : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ endpointSelectionError a b c := by
  unfold endpointSelectionError; positivity

theorem endpointSelectionError_tendsto (a b : ℝ) {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0)) :
    Tendsto (fun n => endpointSelectionError a b (c n)) atTop (𝓝 0) := by
  simpa only [endpointSelectionError, mul_zero] using hc.const_mul (8 * (|a| + |b| + 1))

variable {ι : Type*} [Fintype ι]

/-- A selected polygon: a cap in the box `[a, b] × [0, 1]`, equal to its circumscription by unit
normals with positive second coordinates and injective wall slopes, maximizing the finite score
minus the support penalty towards `target` among all boxed caps. The penalty weights are
nonnegative with total at most `c`. -/
structure IsSelected (normal : ι → Plane) (corners : List (ι × ι)) (terminal : Option ι)
    (weight : ι → ℝ) (target : Set Plane) (a b c : ℝ) (U : Set Plane) : Prop where
  normal_unit : ∀ i, ∃ θ, normal i = unitNormal θ
  normal_snd_pos : ∀ i, 0 < (normal i).2
  slope_injective : Function.Injective (wallSlope normal)
  weight_nonneg : ∀ i, 0 ≤ weight i
  sum_weight_le : ∑ i, weight i ≤ c
  isCap : IsDownwardCap U
  inBox : U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1
  polygon_eq : U = circumscription U normal
  maximizes : ∀ V : Set Plane, IsDownwardCap V → V ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 →
    finiteSpatialScore V normal corners terminal -
        sampledPenalty V normal weight (fun i => support target (normal i)) ≤
      finiteSpatialScore U normal corners terminal -
        sampledPenalty U normal weight (fun i => support target (normal i))

namespace IsSelected

variable {normal : ι → Plane} {corners : List (ι × ι)} {terminal : Option ι}
  {weight : ι → ℝ} {target U : Set Plane} {a b c : ℝ}
  (hU : IsSelected normal corners terminal weight target a b c U)
include hU

theorem coefficient_nonneg : 0 ≤ c :=
  (Finset.sum_nonneg fun i _ => hU.weight_nonneg i).trans hU.sum_weight_le

theorem supportPenaltyLipschitz_le :
    supportPenaltyLipschitz (|a| + |b| + 1) normal weight ≤ endpointSelectionError a b c := by
  have hsum : (∑ i, weight i * (|(normal i).1| + |(normal i).2|)) ≤ 2 * c :=
    calc _ ≤ ∑ i, weight i * 2 := Finset.sum_le_sum fun i _ => by
          refine mul_le_mul_of_nonneg_left ?_ (hU.weight_nonneg i)
          obtain ⟨θ, hθ⟩ := hU.normal_unit i
          rw [hθ]
          exact (add_le_add (Real.abs_cos_le_one _) (Real.abs_sin_le_one _)).trans_eq
            one_add_one_eq_two
      _ ≤ 2 * c := by rw [← Finset.sum_mul]; linarith [hU.sum_weight_le]
  unfold supportPenaltyLipschitz endpointSelectionError
  linarith [mul_le_mul_of_nonneg_left hsum (show 0 ≤ 4 * (|a| + |b| + 1) by positivity)]

/-- The box bounds the selected points and the target supports in every normal direction. -/
theorem support_bounds (hTarget : IsDownwardCap target)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1) :
    (∀ p ∈ U, ∀ i, |coordDot p (normal i)| ≤ |a| + |b| + 1) ∧
      ∀ i, |support target (normal i)| ≤ |a| + |b| + 1 := by
  have h (p : Plane) (hp : p ∈ Icc a b ×ˢ Icc (0 : ℝ) 1) (i : ι) :
      |coordDot p (normal i)| ≤ |a| + |b| + 1 := by
    obtain ⟨θ, hθ⟩ := hU.normal_unit i
    rw [hθ]; exact abs_coordDot_unitNormal_le_box hp _
  exact ⟨fun p hp => h p (hU.inBox hp),
    fun i => abs_support_le_of_pointwise_bound hTarget _ fun p hp => h p (hTargetBox hp) i⟩

/-- Inward variations: the erosions from either side and the inward pressure bounds. -/
theorem inward_bounds (hTarget : IsDownwardCap target)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1) (hW : 1 ≤ capWidth U) :
    (finiteRightMoment U normal corners terminal ≤ capRoof U (horizontalRight U) -
        rightEndpointPressure (capRoof U) (finiteBarrier U normal corners terminal)
          (horizontalLeft U) (horizontalRight U) + endpointSelectionError a b c) ∧
    (finiteLeftMoment U normal corners terminal ≤ capRoof U (horizontalLeft U) -
        leftEndpointPressure (capRoof U) (finiteBarrier U normal corners terminal)
          (horizontalLeft U) (horizontalRight U) + endpointSelectionError a b c) ∧
    rightEndpointPressure (capRoof U) (finiteBarrier U normal corners terminal)
        (horizontalLeft U) (horizontalRight U) ≤
      capRoof U (horizontalRight U) + endpointSelectionError a b c ∧
    leftEndpointPressure (capRoof U) (finiteBarrier U normal corners terminal)
        (horizontalLeft U) (horizontalRight U) ≤
      capRoof U (horizontalLeft U) + endpointSelectionError a b c := by
  have hC := hU.isCap
  obtain ⟨hpoints, htargets⟩ := hU.support_bounds hTarget hTargetBox
  have hmax V hV (hVU : V ⊆ U) := hU.maximizes V hV (hVU.trans hU.inBox)
  have hlip := hU.supportPenaltyLipschitz_le
  have hE := selected_erosion_moment hC hW _ hU.normal_snd_pos hU.slope_injective hU.polygon_eq
    corners terminal _ _ _ (by positivity) hU.weight_nonneg hpoints htargets hmax
  have hR := selected_right_inward_pressure hC hW _ (fun i => (hU.normal_snd_pos i).le) corners
    terminal _ _ _ (by positivity) hU.weight_nonneg hpoints htargets hmax
  have hL := selected_left_inward_pressure hC hW _ (fun i => (hU.normal_snd_pos i).le) corners
    terminal _ _ _ (by positivity) hU.weight_nonneg hpoints htargets hmax
  refine ⟨?_, ?_, by linarith, by linarith⟩
  · rw [finiteRightMoment, rightErosionVelocity]
    linarith [hE (rightErosion U) 0 (-1) (fun i => -max (normal i).1 0) fun ε h0 hε =>
      ⟨hC.rightErosion h0 hε, rightErosion_subset U ε, abs_support_rightErosion_sub_le hC hW h0 hε,
        by rw [horizontalLeft_rightErosion hC h0 hε]; ring,
        by rw [horizontalRight_rightErosion hC h0 hε]; ring, by
          simpa only [mul_zero, add_zero, mul_neg, mul_one, ← sub_eq_add_neg] using
            (congrArg (rightErosion · ε) hU.polygon_eq).trans
              (rightErosion_upperPolygon normal _ h0)⟩]
  · rw [finiteLeftMoment, leftErosionVelocity]
    linarith [hE (leftErosion U) 1 0 (fun i => -max (-(normal i).1) 0) fun ε h0 hε =>
      ⟨hC.leftErosion h0 hε, leftErosion_subset U ε, abs_support_leftErosion_sub_le hC hW h0 hε,
        by rw [horizontalLeft_leftErosion hC h0 hε]; ring,
        by rw [horizontalRight_leftErosion hC h0 hε]; ring, by
          simpa only [mul_zero, add_zero, mul_neg, mul_one, ← sub_eq_add_neg] using
            (congrArg (leftErosion · ε) hU.polygon_eq).trans
              (leftErosion_upperPolygon normal _ h0)⟩]

/-- A positive right end face has an actual outward competitor. The
strict box slack is used only to keep this small competitor in the box. -/
theorem right_height_le_pressure (hslack : horizontalRight U < b) :
    capRoof U (horizontalRight U) ≤
      max (rightEndpointPressure (capRoof U) (finiteBarrier U normal corners terminal)
        (horizontalLeft U) (horizontalRight U)) 0 := by
  refine (le_or_gt (capRoof U (horizontalRight U)) 0).elim (le_max_of_le_right ·) fun he =>
    le_max_of_le_left ?_
  have hC := hU.isCap
  let height : ι → ℝ := fun i => support U (normal i)
  let F : ℝ → ℝ := fun ε => intervalSpatialScore (roofEnvelope normal height)
    (barrierEnvelope normal height corners terminal) (horizontalLeft U) (horizontalRight U + ε)
  have hlr := horizontalLeft_le_horizontalRight hC.nonempty hC.isCompact
  have hroof := eqOn_roofEnvelope_of_circumscription hC normal hU.normal_snd_pos hU.polygon_eq
  have hbarrier : barrierEnvelope normal height corners terminal =
      finiteBarrier U normal corners terminal :=
    funext fun x => (finiteBarrier_eq_eval _ height (fun _ => rfl) _ _ x).symm
  have hzero : F 0 = finiteSpatialScore U normal corners terminal := by
    simp only [F, add_zero, hbarrier]; exact intervalSpatialScore_congr_roof hlr hroof
  obtain ⟨δ, hδ, hfamily⟩ := exists_right_axis_variation normal height hlr hU.normal_snd_pos
    (circumscription_baseline hC normal) (support_circumscription hC normal)
    (subset_circumscription hC _
      (capRoof_mem hC.isCompact (horizontalRight_mem hC.nonempty hC.isCompact))) he
  have hleftBox : a ≤ horizontalLeft U := (hU.inBox (hC.baseline_mem_of_mem_projection
    (horizontalLeft_mem hC.nonempty hC.isCompact))).1.1
  have hmax : ∀ᶠ ε in 𝓝[>] (0 : ℝ), F ε ≤ F 0 := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min hδ (sub_pos.mpr hslack))] with ε ⟨hε0, hε⟩
    obtain ⟨hV, hbase, _, hsupport⟩ := hfamily ε ⟨hε0.le, hε.trans_le (min_le_left _ _)⟩
    have h := hU.maximizes _ hV fun p hp => by
      obtain ⟨hx, hy, _⟩ := (mem_upperPolygon_iff _ _ _ _ _).mp hp
      exact ⟨⟨hleftBox.trans hx.1, by linarith [hx.2, hε.trans_le (min_le_right _ _)]⟩, hy⟩
    have hpen : sampledPenalty (upperPolygon (horizontalLeft U) (horizontalRight U + ε) normal
        height) normal weight (fun i => support target (normal i)) =
        sampledPenalty U normal weight (fun i => support target (normal i)) := by
      simp only [sampledPenalty, hsupport]; rfl
    have hscore : finiteSpatialScore (upperPolygon _ _ normal height) normal corners terminal =
        F ε := finiteSpatialScore_upperPolygon _ height (by linarith) hU.normal_snd_pos hbase
      hsupport _ _
    rw [hpen, hscore, ← hzero] at h
    linarith
  have hsign := hasDerivAt_nonpos_of_right_max (f := F) (hasDerivAt_intervalSpatialScore_right
    (continuous_roofEnvelope normal height)
    (continuous_barrierEnvelope normal height corners terminal) _ _) hmax
  rw [← hbarrier, ← rightEndpointPressure_congr_roof hlr hroof, ← hroof ⟨hlr, le_rfl⟩]
  unfold rightEndpointPressure
  linarith

theorem left_height_le_pressure (hslack : a < horizontalLeft U) :
    capRoof U (horizontalLeft U) ≤
      max (leftEndpointPressure (capRoof U) (finiteBarrier U normal corners terminal)
        (horizontalLeft U) (horizontalRight U)) 0 := by
  refine (le_or_gt (capRoof U (horizontalLeft U)) 0).elim (le_max_of_le_right ·) fun he =>
    le_max_of_le_left ?_
  have hC := hU.isCap
  let height : ι → ℝ := fun i => support U (normal i)
  let F : ℝ → ℝ := fun ε => intervalSpatialScore (roofEnvelope normal height)
    (barrierEnvelope normal height corners terminal) (horizontalLeft U - ε) (horizontalRight U)
  have hlr := horizontalLeft_le_horizontalRight hC.nonempty hC.isCompact
  have hroof := eqOn_roofEnvelope_of_circumscription hC normal hU.normal_snd_pos hU.polygon_eq
  have hbarrier : barrierEnvelope normal height corners terminal =
      finiteBarrier U normal corners terminal :=
    funext fun x => (finiteBarrier_eq_eval _ height (fun _ => rfl) _ _ x).symm
  have hzero : F 0 = finiteSpatialScore U normal corners terminal := by
    simp only [F, sub_zero, hbarrier]; exact intervalSpatialScore_congr_roof hlr hroof
  obtain ⟨δ, hδ, hfamily⟩ := exists_left_axis_variation normal height hlr hU.normal_snd_pos
    (circumscription_baseline hC normal) (support_circumscription hC normal)
    (subset_circumscription hC _
      (capRoof_mem hC.isCompact (horizontalLeft_mem hC.nonempty hC.isCompact))) he
  have hrightBox : horizontalRight U ≤ b := (hU.inBox (hC.baseline_mem_of_mem_projection
    (horizontalRight_mem hC.nonempty hC.isCompact))).1.2
  have hmax : ∀ᶠ ε in 𝓝[>] (0 : ℝ), F ε ≤ F 0 := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min hδ (sub_pos.mpr hslack))] with ε ⟨hε0, hε⟩
    obtain ⟨hV, hbase, _, hsupport⟩ := hfamily ε ⟨hε0.le, hε.trans_le (min_le_left _ _)⟩
    have h := hU.maximizes _ hV fun p hp => by
      obtain ⟨hx, hy, _⟩ := (mem_upperPolygon_iff _ _ _ _ _).mp hp
      exact ⟨⟨by linarith [hx.1, hε.trans_le (min_le_right _ _)], hx.2.trans hrightBox⟩, hy⟩
    have hpen : sampledPenalty (upperPolygon (horizontalLeft U - ε) (horizontalRight U) normal
        height) normal weight (fun i => support target (normal i)) =
        sampledPenalty U normal weight (fun i => support target (normal i)) := by
      simp only [sampledPenalty, hsupport]; rfl
    have hscore : finiteSpatialScore (upperPolygon _ _ normal height) normal corners terminal =
        F ε := finiteSpatialScore_upperPolygon _ height (by linarith) hU.normal_snd_pos hbase
      hsupport _ _
    rw [hpen, hscore, ← hzero] at h
    linarith
  have hsign := hasDerivAt_nonpos_of_right_max (f := F) (hasDerivAt_intervalSpatialScore_left
    (continuous_roofEnvelope normal height)
    (continuous_barrierEnvelope normal height corners terminal) _ _) hmax
  rw [← hbarrier, ← leftEndpointPressure_congr_roof hlr hroof, ← hroof ⟨le_rfl, hlr⟩]
  unfold leftEndpointPressure
  linarith

/-- Finite approximate complementarity, including zero end heights. -/
theorem abs_complementarity_le (hTarget : IsDownwardCap target)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1) (hW : 1 ≤ capWidth U) :
    (horizontalRight U < b → |capRoof U (horizontalRight U) -
      max (rightEndpointPressure (capRoof U) (finiteBarrier U normal corners terminal)
        (horizontalLeft U) (horizontalRight U)) 0| ≤ endpointSelectionError a b c) ∧
    (a < horizontalLeft U → |capRoof U (horizontalLeft U) -
      max (leftEndpointPressure (capRoof U) (finiteBarrier U normal corners terminal)
        (horizontalLeft U) (horizontalRight U)) 0| ≤ endpointSelectionError a b c) := by
  have hK0 := endpointSelectionError_nonneg a b hU.coefficient_nonneg
  have h0 := capRoof_nonneg hU.isCap.isCompact (fun p hp => (hU.isCap.inStrip hp).1)
  obtain ⟨-, -, hR, hL⟩ := hU.inward_bounds hTarget hTargetBox hW
  exact ⟨fun hslack => abs_le.mpr ⟨by linarith [max_le hR (add_nonneg (h0 _) hK0)],
      by linarith [hU.right_height_le_pressure hslack]⟩,
    fun hslack => abs_le.mpr ⟨by linarith [max_le hL (add_nonneg (h0 _) hK0)],
      by linarith [hU.left_height_le_pressure hslack]⟩⟩

end IsSelected

end FinitePolygon

namespace AngularGrid

open FinitePolygon

theorem IsSelectedPolygon.isSelected {target U : Set Plane} {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hc : 0 ≤ coefficient) :
    IsSelected (normal (dyadic level)) (pairList (dyadic level)) none
      (fun i => coefficient * stageWeight level i) target a b coefficient U where
  normal_unit i := ⟨_, normal_eq_unitNormal _ i⟩
  normal_snd_pos := normal_snd_pos _
  slope_injective := wallSlopes_injective _
  weight_nonneg i := mul_nonneg hc (stageWeight_nonneg level i)
  sum_weight_le := by
    rw [← Finset.mul_sum]; exact mul_le_of_le_one_right hc (sum_stageWeight_le_one level)
  isCap := hU.isCap
  inBox := hU.inBox
  polygon_eq := hU.polygon_eq
  maximizes V hV hVB := by
    simpa only [score, stagePenalty, sampledPenalty_mul] using hU.maximizes V hV hVB

end AngularGrid

end AmbidextrousSofa
