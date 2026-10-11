module

public import AmbidextrousSofa.Analysis.RoofGain

@[expose] public section

/-!
# Actual point insertion in inactive supporting directions

The maximum baseline wall slack on an interval is attained at one of its
two endpoints. If every supporting direction of an actual roof point has
strictly negative middle slack, compactness of the entire upper semicircle
gives a uniform insertion radius. Each changed support then has a wall that
excludes the whole positive-height forbidden quadrant on the middle.

The proof takes the supremum over every real turning angle. It does not
select one active angle, neglect an attached wall, or identify a limiting
niche measure with the arc length of a limiting positive graph.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

/-- Maximum baseline slack of one actual inner support wall on `[a,b]`. -/
def middleWallSlack (U : Set Plane) (a b θ : ℝ) : ℝ :=
  angleSupport U θ - 1 - min (a * Real.cos θ) (b * Real.cos θ)

theorem continuous_middleWallSlack {U : Set Plane} (hU : IsCompact U) (a b : ℝ) :
    Continuous (middleWallSlack U a b) := by
  have := continuous_angleSupport hU
  unfold middleWallSlack
  fun_prop

theorem baseline_slack_le_middleWallSlack (U : Set Plane) {a b x : ℝ}
    (hx : x ∈ Icc a b) (θ : ℝ) :
    angleSupport U θ - 1 - coordDot (x, 0) (unitNormal θ) ≤
      middleWallSlack U a b θ := by
  have : min (a * Real.cos θ) (b * Real.cos θ) ≤ x * Real.cos θ := by
    rcases le_total 0 (Real.cos θ) with hc | hc
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx.1 hc)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx.2 hc)
  simp only [coordDot, unitNormal, middleWallSlack]
  linarith

/-- An unchanged wall or a wall excluding all positive heights is enough:
the complete positive corner envelope is unchanged. -/
theorem clippedCorner_eq_of_support_eq_or_inactive {U V : Set Plane}
    (hU : IsDownwardCap U) (hV : IsDownwardCap V) (hUV : U ⊆ V)
    {θ x : ℝ} (hθ : θ ∈ Ioo 0 (Real.pi / 2))
    (hfirst : support V (unitNormal θ) = support U (unitNormal θ) ∨
      support V (unitNormal θ) - 1 ≤ coordDot (x, 0) (unitNormal θ))
    (hsecond : support V (companionNormal θ) = support U (companionNormal θ) ∨
      support V (companionNormal θ) - 1 ≤ coordDot (x, 0) (companionNormal θ)) :
    max (cornerWall V θ x) 0 = max (cornerWall U θ x) 0 := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.1, hθ.2])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, hθ.2], hθ.2⟩
  have hzero (h : cornerWall V θ x ≤ 0) :
      max (cornerWall V θ x) 0 = max (cornerWall U θ x) 0 := by
    rw [max_eq_right h, max_eq_right (show cornerWall U θ x ≤ 0 from (min_le_min
      (firstWall_mono hUV hU.nonempty hV.isCompact hs x)
      (secondWall_mono hUV hU.nonempty hV.isCompact hc x)).trans h)]
  rcases hfirst with hfirst | hfirst
  · rcases hsecond with hsecond | hsecond
    · simp only [cornerWall, firstWall, secondWall, hfirst, hsecond]
    · exact hzero ((min_le_right _ _).trans ((secondWall_le_iff hc).mpr hsecond))
  · exact hzero ((min_le_left _ _).trans ((firstWall_le_iff hs).mpr hfirst))

theorem sweptNiche_eq_of_support_eq_or_inactive {U V : Set Plane}
    (hU : IsDownwardCap U) (hV : IsDownwardCap V) (hUV : U ⊆ V) {x : ℝ}
    (hwalls : ∀ θ ∈ Ioo 0 Real.pi,
      support V (unitNormal θ) = support U (unitNormal θ) ∨
        support V (unitNormal θ) - 1 ≤ coordDot (x, 0) (unitNormal θ)) :
    sweptNiche V (Real.pi / 2) x = sweptNiche U (Real.pi / 2) x := by
  refine le_antisymm (sweptNiche_le_of_forall (by positivity) (sweptNiche_nonneg U _ x)
    fun θ hθ => ?_) (sweptNiche_mono hUV hU.nonempty hV.isCompact (by positivity) le_rfl x)
  have hsecond := hwalls (θ + Real.pi / 2) ⟨by linarith [hθ.1, hθ.2], by linarith [hθ.2]⟩
  rw [← companionNormal_eq_unitNormal θ] at hsecond
  exact (le_max_left _ _).trans <| (clippedCorner_eq_of_support_eq_or_inactive hU hV hUV hθ
    (hwalls θ ⟨hθ.1, by linarith [hθ.1, hθ.2]⟩) hsecond).trans_le <| max_le
    (cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCompact le_rfl x) hθ)
    (sweptNiche_nonneg U _ x)

/-- Uniform separation is taken on the entire compact upper semicircle.
At each direction either the old point is strictly below the support or
that wall is strictly inactive throughout the middle interval. -/
theorem IsDownwardCap.exists_inactive_insertion_radius {U : Set Plane}
    (hU : IsDownwardCap U) {p : Plane} (hp : p ∈ U) {a b : ℝ}
    (hinactive : ∀ θ ∈ Icc 0 Real.pi,
      coordDot p (unitNormal θ) = angleSupport U θ → middleWallSlack U a b θ < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < δ → p.2 + ε ≤ 1 →
      EqOn (sweptNiche (insertedCap U (p.1, p.2 + ε)) (Real.pi / 2))
        (sweptNiche U (Real.pi / 2)) (Icc a b) := by
  have hmargin : Continuous fun θ =>
      max (angleSupport U θ - coordDot p (unitNormal θ)) (-middleWallSlack U a b θ) :=
    ((continuous_angleSupport hU.isCompact).sub ((continuous_coordDot_left p).comp
      continuous_unitNormal)).max (continuous_middleWallSlack hU.isCompact a b).neg
  obtain ⟨δ, hδ, hbound⟩ := isCompact_Icc.exists_forall_le' hmargin.continuousOn fun θ hθ => by
    rcases (sub_nonneg.mpr (coordDot_le_support hU.isCompact hp (unitNormal θ))).lt_or_eq
      with h | h
    · exact h.trans_le (le_max_left _ _)
    · exact (neg_pos.mpr (hinactive θ hθ (sub_eq_zero.mp h.symm).symm)).trans_le
        (le_max_right _ _)
  refine ⟨δ, hδ, fun ε hε hεδ htop x hx => ?_⟩
  have hq : (p.1, p.2 + ε) ∈ unitStrip := ⟨by linarith [(hU.inStrip hp).1], htop⟩
  refine sweptNiche_eq_of_support_eq_or_inactive hU (hU.isDownwardCap_insertedCap hq)
    (hU.subset_insertedCap hq) fun θ hθ => ?_
  have hs : 0 ≤ Real.sin θ := (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).le
  have hdot : coordDot (p.1, p.2 + ε) (unitNormal θ) =
      coordDot p (unitNormal θ) + ε * Real.sin θ := by
    simp only [coordDot, unitNormal]
    ring
  have hsin := mul_le_of_le_one_right hε (Real.sin_le_one θ)
  have hpSupport := coordDot_le_support hU.isCompact hp (unitNormal θ)
  rcases le_max_iff.mp (hbound θ ⟨hθ.1.le, hθ.2.le⟩) with hgap | hslack
  · unfold angleSupport at hgap
    refine .inl (hU.support_insertedCap_eq_of_dominated hq hs ?_)
    rw [hdot]
    linarith
  · have := baseline_slack_le_middleWallSlack U hx θ
    unfold angleSupport at this
    refine .inr ?_
    rw [hU.support_insertedCap hq hs, hdot, sub_le_iff_le_add]
    exact max_le (by linarith) (by linarith)

/-- Every charged roof point below the top of a global maximizer has an
actual supporting normal whose middle wall is not strictly inactive. -/
theorem IsFullCapMaximizer.exists_noninactive_normal_on_wing {U : Set Plane}
    (hU : IsFullCapMaximizer U) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Icc (horizontalLeft U)
        (horizontalLeft U + capWidth U / 4) ∪
      Icc (horizontalRight U - capWidth U / 4) (horizontalRight U))
    (hlow : capRoof U x₀ < 1) :
    ∃ θ ∈ Icc 0 Real.pi,
      coordDot (x₀, capRoof U x₀) (unitNormal θ) = angleSupport U θ ∧
      0 ≤ middleWallSlack U (horizontalLeft U + capWidth U / 4)
        (horizontalRight U - capWidth U / 4) θ := by
  -- Otherwise a small vertical insertion at the roof point would raise the score.
  by_contra! h
  have hC := hU.isCap
  have hwidth : 0 < capWidth U := by linarith [hU.width_bounds.1, one_lt_M]
  have hxU : x₀ ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hC.nonempty hC.isCompact hC.convex]
    unfold capWidth at hwidth hx₀
    rcases hx₀ with hx₀ | hx₀ <;> constructor <;> linarith [hx₀.1, hx₀.2]
  have hp := capRoof_mem hC.isCompact hxU
  obtain ⟨δ, hδ, hδworks⟩ := hC.exists_inactive_insertion_radius hp h
  obtain ⟨ε, hε, hεmin⟩ := exists_between (lt_min hδ (sub_pos.2 hlow))
  obtain ⟨hεδ, hεtop⟩ := lt_min_iff.mp hεmin
  have hq : (x₀, capRoof U x₀ + ε) ∈ unitStrip :=
    ⟨by linarith [(hC.inStrip hp).1], by linarith⟩
  have hV := hC.isDownwardCap_insertedCap hq
  have hgain : capRoof U x₀ + ε ≤ _ := le_capRoof hV.isCompact (inserted_point_mem hq)
  refine (hC.capScore_lt_of_charged_roof_gain hV (hC.subset_insertedCap hq)
    (hC.horizontalProjection_insertedCap hq hxU) hwidth (fun x hx => ?_) hx₀
    (by linarith)).not_ge (hU.2 _ hV)
  rw [hV.partialBarrier_pi_div_two, hC.partialBarrier_pi_div_two]
  exact hδworks ε hε.le hεδ (by linarith) hx

end AmbidextrousSofa
