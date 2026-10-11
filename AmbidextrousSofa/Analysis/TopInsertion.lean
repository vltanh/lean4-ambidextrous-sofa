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
partial barrier are unchanged there. For nested caps with the same
projection and the same middle barrier, a strict roof gain at a point of a
charged wing strictly increases the score; so inserting at the right end of
the middle window strictly increases the full-turn score if its old roof is
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

/-- For nested caps with the same projection, a strict roof increase at a point of either
charged wing gives a strict score increase whenever the whole middle barrier is unchanged. -/
theorem IsDownwardCap.capScore_lt_of_charged_roof_gain {U V : Set Plane}
    (hU : IsDownwardCap U) (hV : IsDownwardCap V) (hUV : U ⊆ V)
    (hproj : horizontalProjection V = horizontalProjection U)
    (hwidth : 0 < capWidth U) {α x₀ : ℝ}
    (hniche : EqOn (partialBarrier V α) (partialBarrier U α)
      (middleHalfInterval (horizontalLeft U) (horizontalRight U)))
    (hx₀ : x₀ ∈ Icc (horizontalLeft U)
        (horizontalLeft U + capWidth U / 4) ∪
      Icc (horizontalRight U - capWidth U / 4) (horizontalRight U))
    (hgain : capRoof U x₀ < capRoof V x₀) : capScore U α < capScore V α := by
  have hleft : horizontalLeft V = horizontalLeft U := congrArg sInf hproj
  have hright : horizontalRight V = horizontalRight U := congrArg sSup hproj
  have hcU := hU.continuousOn_capRoof_Icc
  have hcV := hV.continuousOn_capRoof_Icc
  rw [hleft, hright] at hcV
  set l := horizontalLeft U
  set r := horizontalRight U
  have hw : 0 < r - l := hwidth
  have hle {c d} (hc : l ≤ c) (hcd : c ≤ d) (hd : d ≤ r) :
      (∫ x in c..d, capRoof U x) ≤ ∫ x in c..d, capRoof V x :=
    intervalIntegral.integral_mono_on hcd
      ((hcU.mono (Icc_subset_Icc hc hd)).intervalIntegrable_of_Icc hcd)
      ((hcV.mono (Icc_subset_Icc hc hd)).intervalIntegrable_of_Icc hcd)
      fun x _ => hU.capRoof_mono hV hUV x
  have hlt {c d} (hc : l ≤ c) (hcd : c < d) (hd : d ≤ r) (hx : x₀ ∈ Icc c d) :
      (∫ x in c..d, capRoof U x) < ∫ x in c..d, capRoof V x :=
    intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hcd
      (hcU.mono (Icc_subset_Icc hc hd)) (hcV.mono (Icc_subset_Icc hc hd))
      (fun x _ => hU.capRoof_mono hV hUV x) ⟨x₀, hx, hgain⟩
  have hmid : (∫ x in (l + (r - l) / 4)..(r - (r - l) / 4), partialBarrier V α x) =
      ∫ x in (l + (r - l) / 4)..(r - (r - l) / 4), partialBarrier U α x :=
    intervalIntegral.integral_congr fun x hx => hniche (by rwa [uIcc_of_le (by linarith)] at hx)
  rw [hU.capScore_eq_intervalSpatialScore, hV.capScore_eq_intervalSpatialScore, hleft, hright,
    intervalSpatialScore, intervalSpatialScore, hmid]
  have := hle le_rfl (by linarith : l ≤ l + (r - l) / 4) (by linarith)
  have := hle (by linarith) (by linarith : r - (r - l) / 4 ≤ r) le_rfl
  rcases hx₀ with hx₀ | hx₀
  · linarith [hlt le_rfl (by linarith : l < l + (r - l) / 4) (by linarith) hx₀]
  · linarith [hlt (by linarith) (by linarith : r - (r - l) / 4 < r) le_rfl hx₀]

theorem IsFullCapMaximizer.middle_right_eq_one_of_top_right {U : Set Plane}
    (hU : IsFullCapMaximizer U) {t : ℝ} (ht : (t, 1) ∈ U)
    (htRight : horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 ≤ t) :
    capRoof U (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) = 1 := by
  have hC := hU.isCap
  have hw : 0 < capWidth U := (zero_lt_one.trans one_lt_M).trans_le hU.width_bounds.1
  set b := horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 with hb_def
  have hp : (b, (1 : ℝ)) ∈ unitStrip := ⟨zero_le_one, le_rfl⟩
  have hb : b ∈ horizontalProjection U := by
    rw [hC.horizontalProjection_eq_Icc]
    unfold capWidth at hw
    constructor <;> linarith
  -- If the roof at the inserted point were below one, the insertion would raise the score: the
  -- charged right wing gains strictly, and the middle barrier is unchanged.
  refine le_antisymm (capRoof_le_one hC.isCompact hC.inStrip _) (not_lt.1 fun hlow =>
    (hU.2 _ (hC.isDownwardCap_insertedCap hp)).not_gt ?_)
  exact hC.capScore_lt_of_charged_roof_gain (x₀ := b) (hC.isDownwardCap_insertedCap hp)
    (hC.subset_insertedCap hp) (hC.horizontalProjection_insertedCap hp hb) hw
    (fun x hx => hC.partialBarrier_inserted_top_of_top_right ht htRight (by positivity) le_rfl hx.2)
    (.inr ⟨le_rfl, sub_le_self _ (div_nonneg hw.le (by norm_num))⟩)
    (by rwa [hC.capRoof_inserted_one])

end AmbidextrousSofa
