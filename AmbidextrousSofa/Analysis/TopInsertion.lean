module

public import AmbidextrousSofa.Analysis.CapInsertion
public import AmbidextrousSofa.Analysis.GlobalCapMaximum
public import AmbidextrousSofa.Analysis.FiniteScore

@[expose] public section

/-!
# Top insertion preserves the whole niche on the middle window

When an old height-one point lies to the right of an inserted height-one
point, the first supporting wall is unchanged. Any changed second wall is
nonpositive at every abscissa to the left of the inserted point. Thus the
positive part of every corner, and its whole angular supremum, is unchanged
there. Inserting at the right end of the middle window strictly increases
the score if its old roof is below one. This is an actual set variation.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem IsDownwardCap.clippedCorner_inserted_top {U : Set Plane}
    (hU : IsDownwardCap U) {a t θ x : ℝ} (ht : (t, 1) ∈ U) (hat : a ≤ t)
    (hθ : θ ∈ Ioo 0 (Real.pi / 2)) (hxa : x ≤ a) :
    max (cornerWall (insertedCap U (a, 1)) θ x) 0 =
      max (cornerWall U θ x) 0 := by
  have hp : (a, (1 : ℝ)) ∈ unitStrip := ⟨zero_le_one, le_rfl⟩
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  by_cases hdom : coordDot (a, 1) (companionNormal θ) ≤ support U (companionNormal θ)
  · rw [cornerWall, cornerWall, firstWall, firstWall, secondWall, secondWall,
      hU.support_insertedCap_eq_of_dominated hp hc.le hdom,
      hU.support_insertedCap_eq_of_dominated hp hs.le (le_trans
        (by simp only [coordDot, unitNormal]; nlinarith) (coordDot_le_support hU.isCompact ht _))]
  have hsecond : secondWall (insertedCap U (a, 1)) θ x ≤ 0 := by
    rw [secondWall_le_iff hc, hU.support_insertedCap hp hc.le, max_eq_right (le_of_not_ge hdom)]
    simp only [coordDot, companionNormal]
    nlinarith [Real.cos_le_one θ]
  rw [cornerWall, cornerWall, max_eq_right ((min_le_right _ _).trans hsecond),
    max_eq_right ((min_le_right _ _).trans ((secondWall_mono (hU.subset_insertedCap hp)
      hU.nonempty (hU.isDownwardCap_insertedCap hp).isCompact hc x).trans hsecond))]

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
    rw [horizontalProjection_eq_Icc hC.nonempty hC.isCompact hC.convex]
    constructor <;> linarith
  have hmono := hC.capRoof_mono hV (hC.subset_insertedCap hp)
  -- On the middle window the whole partial barrier is unchanged.
  have hniche : EqOn (partialBarrier (insertedCap U (b, 1)) (Real.pi / 2))
      (partialBarrier U (Real.pi / 2))
      (uIcc (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) b) := fun x hx => by
    have hx : x ≤ b := hx.2.trans (sup_le (by linarith) le_rfl)
    rw [hV.partialBarrier_pi_div_two, hC.partialBarrier_pi_div_two]
    refine le_antisymm (sweptNiche_le_of_forall (by positivity) (sweptNiche_nonneg ..)
      fun θ hθ => (le_max_left _ _).trans
        ((hC.clippedCorner_inserted_top ht htRight hθ hx).trans_le (max_le
          (cornerWall_le_sweptNiche (sweptWallValues_bddAbove hC.isCompact le_rfl x) hθ)
          (sweptNiche_nonneg ..))))
      (sweptNiche_mono (hC.subset_insertedCap hp) hC.nonempty hV.isCompact (by positivity) le_rfl x)
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
