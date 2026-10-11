module

public import AmbidextrousSofa.Analysis.CapInsertion
public import AmbidextrousSofa.Analysis.GlobalCapMaximum
public import AmbidextrousSofa.Analysis.FiniteScore

@[expose] public section

/-!
# Top insertion preserves the whole barrier on the middle window

When an old height-one point lies to the right of an inserted height-one
point, the first supporting walls are unchanged. Any changed second wall is
nonpositive at every abscissa to the left of the inserted point. Thus the
positive part of every corner, its whole angular supremum, and the whole
partial barrier are unchanged there. Inserting at the right end of the
middle window strictly increases the full-turn score if its old roof is
below one. This is an actual set variation.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

/-- Clipped corners bounded at every visited angle by those of a compact set bound the swept
niche. -/
theorem sweptNiche_le_of_clippedCorner_le {U V : Set Plane} (hV : IsCompact V) {α x : ℝ}
    (hα0 : 0 < α) (hα : α ≤ Real.pi / 2)
    (hle : ∀ θ ∈ Ioo 0 α, max (cornerWall U θ x) 0 ≤ max (cornerWall V θ x) 0) :
    sweptNiche U α x ≤ sweptNiche V α x :=
  sweptNiche_le_of_forall hα0 (sweptNiche_nonneg _ _ _) fun θ hθ =>
    (le_max_left _ _).trans <| (hle θ hθ).trans <| max_le
      (cornerWall_le_sweptNiche (sweptWallValues_bddAbove hV hα x) hθ) (sweptNiche_nonneg _ _ _)

/-- Insertion from the right keeps every first wall, including the whole terminal first wall;
a changed second wall is nonpositive at `x`. So the whole partial barrier is unchanged. -/
theorem IsDownwardCap.partialBarrier_inserted_top_of_top_right {U : Set Plane}
    (hU : IsDownwardCap U) {a t α x : ℝ} (ht : (t, 1) ∈ U) (hat : a ≤ t)
    (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) (hxa : x ≤ a) :
    partialBarrier (insertedCap U (a, 1)) α x = partialBarrier U α x := by
  have hp : (a, (1 : ℝ)) ∈ unitStrip := ⟨zero_le_one, le_rfl⟩
  have hV := (hU.isDownwardCap_insertedCap hp).isCompact
  have hfirst {θ : ℝ} (hs : 0 < Real.sin θ) (hc : 0 ≤ Real.cos θ) :
      firstWall (insertedCap U (a, 1)) θ x = firstWall U θ x := by
    rw [firstWall, firstWall, hU.support_insertedCap_eq_of_dominated hp hs.le (le_trans (by
      simp only [coordDot, unitNormal]; linarith [mul_nonneg (sub_nonneg.mpr hat) hc])
      (coordDot_le_support hU.isCompact ht _))]
  have hcorner θ (hθ : θ ∈ Ioo 0 α) :
      max (cornerWall (insertedCap U (a, 1)) θ x) 0 = max (cornerWall U θ x) 0 := by
    obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ⟨hθ.1, hθ.2.trans_le hα⟩
    by_cases hdom : coordDot (a, 1) (companionNormal θ) ≤ support U (companionNormal θ)
    · rw [cornerWall, cornerWall, hfirst hs hc.le, secondWall, secondWall,
        hU.support_insertedCap_eq_of_dominated hp hc.le hdom]
    have hsecond : secondWall (insertedCap U (a, 1)) θ x ≤ 0 := by
      rw [secondWall_le_iff hc, hU.support_insertedCap hp hc.le, max_eq_right (le_of_not_ge hdom)]
      simp only [coordDot, companionNormal]
      nlinarith [Real.cos_le_one θ]
    rw [cornerWall, cornerWall, max_eq_right ((min_le_right _ _).trans hsecond),
      max_eq_right ((min_le_right _ _).trans ((secondWall_mono (hU.subset_insertedCap hp)
        hU.nonempty hV hc x).trans hsecond))]
  rw [partialBarrier, partialBarrier, hfirst (Real.sin_pos_of_pos_of_lt_pi hα0 (by
      linarith [Real.pi_pos])) (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hα⟩),
    le_antisymm (sweptNiche_le_of_clippedCorner_le hU.isCompact hα0 hα fun θ hθ =>
      (hcorner θ hθ).le) (sweptNiche_le_of_clippedCorner_le hV hα0 hα fun θ hθ =>
        (hcorner θ hθ).ge)]

theorem IsFullCapMaximizer.middle_right_eq_one_of_top_right {U : Set Plane}
    (hU : IsFullCapMaximizer U) {t : ℝ} (ht : (t, 1) ∈ U)
    (htRight : horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 ≤ t) :
    capRoof U (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) = 1 := by
  have hC := hU.isCap
  have hlr : horizontalLeft U < horizontalRight U :=
    sub_pos.1 ((zero_lt_one.trans one_lt_M).trans_le hU.width_bounds.1)
  set b := horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 with hb_def
  have hp : (b, (1 : ℝ)) ∈ unitStrip := ⟨zero_le_one, le_rfl⟩
  have hV := hC.isDownwardCap_insertedCap hp
  have hb : b ∈ horizontalProjection U := by
    rw [hC.horizontalProjection_eq_Icc]
    constructor <;> linarith
  have hmono := hC.capRoof_mono hV (hC.subset_insertedCap hp)
  -- On the middle window the whole partial barrier is unchanged.
  have hniche : EqOn (partialBarrier (insertedCap U (b, 1)) (Real.pi / 2))
      (partialBarrier U (Real.pi / 2))
      (uIcc (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) b) := fun x hx =>
    hC.partialBarrier_inserted_top_of_top_right ht htRight (by positivity) le_rfl
      (hx.2.trans (sup_le (by linarith) le_rfl))
  have hl := hC.horizontalLeft_insertedCap hp hb
  have hr := hC.horizontalRight_insertedCap hp hb
  have hcV := hV.continuousOn_capRoof_Icc
  rw [hl, hr] at hcV
  -- If the roof at the inserted point were below one, the insertion would raise the score: the
  -- charged right wing gains strictly, and the middle barrier is unchanged.
  refine le_antisymm (capRoof_le_one hC.isCompact hC.inStrip _)
    (not_lt.1 fun hlow => (hU.2 _ hV).not_gt ?_)
  rw [hC.capScore_eq_intervalSpatialScore, hV.capScore_eq_intervalSpatialScore, hl, hr,
    intervalSpatialScore, intervalSpatialScore, ← hb_def, intervalIntegral.integral_congr hniche]
  exact sub_lt_sub_right (add_lt_add_of_le_of_lt (intervalIntegral.integral_mono (by linarith)
    (hC.intervalIntegrable_capRoof _ _) (hV.intervalIntegrable_capRoof _ _) hmono)
    (intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt (by linarith)
      (hC.continuousOn_capRoof_Icc.mono (Icc_subset_Icc (by linarith) le_rfl))
      (hcV.mono (Icc_subset_Icc (by linarith) le_rfl)) (fun x _ => hmono x)
      ⟨b, ⟨le_rfl, by linarith⟩, by rwa [hC.capRoof_inserted_one]⟩)) _

end AmbidextrousSofa
