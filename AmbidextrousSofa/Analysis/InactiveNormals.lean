import AmbidextrousSofa.Analysis.RoofGain

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
  exact ((continuous_angleSupport hU).sub continuous_const).sub
    ((continuous_const.mul Real.continuous_cos).min
      (continuous_const.mul Real.continuous_cos))

theorem baseline_slack_le_middleWallSlack (U : Set Plane) {a b x : ℝ}
    (hx : x ∈ Icc a b) (θ : ℝ) :
    angleSupport U θ - 1 - coordDot (x, 0) (unitNormal θ) ≤
      middleWallSlack U a b θ := by
  have hmin : min (a * Real.cos θ) (b * Real.cos θ) ≤ x * Real.cos θ := by
    rcases le_total 0 (Real.cos θ) with hc | hc
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx.1 hc)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx.2 hc)
  simp only [coordDot, unitNormal, zero_mul, add_zero]
  unfold middleWallSlack
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
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1
    (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  rcases hfirst with hfirst | hfirst
  · rcases hsecond with hsecond | hsecond
    · simp only [cornerWall, firstWall, secondWall, hfirst, hsecond]
    · have hVzero : cornerWall V θ x ≤ 0 :=
        (min_le_right _ _).trans ((secondWall_le_iff hc).mpr hsecond)
      have hUzero : cornerWall U θ x ≤ 0 :=
        (min_le_right _ _).trans
          ((secondWall_mono hUV hU.nonempty hV.isCompact hc x).trans
            ((secondWall_le_iff hc).mpr hsecond))
      rw [max_eq_right hVzero, max_eq_right hUzero]
  · have hVzero : cornerWall V θ x ≤ 0 :=
      (min_le_left _ _).trans ((firstWall_le_iff hs).mpr hfirst)
    have hUzero : cornerWall U θ x ≤ 0 :=
      (min_le_left _ _).trans
        ((firstWall_mono hUV hU.nonempty hV.isCompact hs x).trans
          ((firstWall_le_iff hs).mpr hfirst))
    rw [max_eq_right hVzero, max_eq_right hUzero]

theorem sweptNiche_eq_of_support_eq_or_inactive {U V : Set Plane}
    (hU : IsDownwardCap U) (hV : IsDownwardCap V) (hUV : U ⊆ V) {x : ℝ}
    (hwalls : ∀ θ ∈ Ioo 0 Real.pi,
      support V (unitNormal θ) = support U (unitNormal θ) ∨
        support V (unitNormal θ) - 1 ≤ coordDot (x, 0) (unitNormal θ)) :
    sweptNiche V (Real.pi / 2) x = sweptNiche U (Real.pi / 2) x := by
  apply le_antisymm
  · apply sweptNiche_le_of_forall (by positivity)
      (sweptNiche_nonneg U (Real.pi / 2) x)
    intro θ hθ
    have hfirst := hwalls θ ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    have hsecond := hwalls (θ + Real.pi / 2)
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
    rw [← companionNormal_eq_unitNormal θ] at hsecond
    calc
      cornerWall V θ x ≤ max (cornerWall V θ x) 0 := le_max_left _ _
      _ = max (cornerWall U θ x) 0 :=
        clippedCorner_eq_of_support_eq_or_inactive hU hV hUV hθ hfirst hsecond
      _ ≤ sweptNiche U (Real.pi / 2) x := max_le
        (cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCompact le_rfl x) hθ)
        (sweptNiche_nonneg U (Real.pi / 2) x)
  · exact sweptNiche_mono hUV hU.nonempty hV.isCompact (by positivity) le_rfl x

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
  let gap := fun θ => angleSupport U θ - coordDot p (unitNormal θ)
  let margin := fun θ => max (gap θ) (-middleWallSlack U a b θ)
  have hgap : Continuous gap := (continuous_angleSupport hU.isCompact).sub
    ((continuous_coordDot_left p).comp continuous_unitNormal)
  have hmargin : Continuous margin := hgap.max
    (continuous_middleWallSlack hU.isCompact a b).neg
  have hpositive : ∀ θ ∈ Icc 0 Real.pi, 0 < margin θ := by
    intro θ hθ
    have hgap0 : 0 ≤ gap θ := sub_nonneg.mpr (coordDot_le_support hU.isCompact hp _)
    by_cases hpos : 0 < gap θ
    · exact hpos.trans_le (le_max_left _ _)
    · have heq : coordDot p (unitNormal θ) = angleSupport U θ := by
        dsimp [gap] at hgap0 hpos
        linarith
      exact (neg_pos.mpr (hinactive θ hθ heq)).trans_le (le_max_right _ _)
  obtain ⟨δ, hδ, hbound⟩ := isCompact_Icc.exists_forall_le'
    hmargin.continuousOn hpositive
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ htop x hx
  let q : Plane := (p.1, p.2 + ε)
  have hq : q ∈ unitStrip := ⟨by dsimp [q]; linarith [(hU.inStrip hp).1], htop⟩
  have hV := hU.isDownwardCap_insertedCap hq
  apply sweptNiche_eq_of_support_eq_or_inactive hU hV (hU.subset_insertedCap hq)
  intro θ hθ
  have hs : 0 ≤ Real.sin θ := (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).le
  have hsin : ε * Real.sin θ ≤ ε := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.sin_le_one θ) hε
  have hdot : coordDot q (unitNormal θ) =
      coordDot p (unitNormal θ) + ε * Real.sin θ := by
    dsimp [q, coordDot, unitNormal]
    ring
  have hpSupport := coordDot_le_support hU.isCompact hp (unitNormal θ)
  have hb := hbound θ ⟨hθ.1.le, hθ.2.le⟩
  change δ ≤ max (gap θ) (-middleWallSlack U a b θ) at hb
  rcases le_max_iff.mp hb with hgapLarge | hinactiveLarge
  · left
    apply hU.support_insertedCap_eq_of_dominated hq hs
    rw [hdot]
    dsimp [gap, angleSupport] at hgapLarge
    linarith
  · right
    have hsupport : angleSupport (insertedCap U q) θ ≤ angleSupport U θ + ε := by
      rw [angleSupport, hU.support_insertedCap hq hs]
      apply max_le
      · change angleSupport U θ ≤ angleSupport U θ + ε
        linarith
      · rw [hdot]
        change _ ≤ support U (unitNormal θ) + ε
        linarith
    have hslack := baseline_slack_le_middleWallSlack U hx θ
    change angleSupport (insertedCap U q) θ - 1 ≤ coordDot (x, 0) (unitNormal θ)
    linarith

/-- A roof point in a charged wing, below height one, can actually be
raised whenever all of its supporting normals are inactive on the middle. -/
theorem IsDownwardCap.exists_score_improving_insertion {U : Set Plane}
    (hU : IsDownwardCap U) (hwidth : 0 < capWidth U) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Icc (horizontalLeft U)
        (horizontalLeft U + capWidth U / 4) ∪
      Icc (horizontalRight U - capWidth U / 4) (horizontalRight U))
    (hlow : capRoof U x₀ < 1)
    (hinactive : ∀ θ ∈ Icc 0 Real.pi,
      coordDot (x₀, capRoof U x₀) (unitNormal θ) = angleSupport U θ →
      middleWallSlack U (horizontalLeft U + capWidth U / 4)
        (horizontalRight U - capWidth U / 4) θ < 0) :
    ∃ ε : ℝ, 0 < ε ∧ capRoof U x₀ + ε < 1 ∧
      capScore U (Real.pi / 2) <
        capScore (insertedCap U (x₀, capRoof U x₀ + ε)) (Real.pi / 2) := by
  have hxU : x₀ ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
    unfold capWidth at hwidth hx₀
    rcases hx₀ with hx₀ | hx₀ <;> constructor <;> linarith [hx₀.1, hx₀.2]
  have hp := capRoof_mem hU.isCompact hxU
  obtain ⟨δ, hδ, hδworks⟩ := hU.exists_inactive_insertion_radius hp hinactive
  let ε := min δ (1 - capRoof U x₀) / 2
  have hmin : 0 < min δ (1 - capRoof U x₀) := lt_min hδ (by linarith)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεδ : ε < δ := by dsimp [ε]; linarith [min_le_left δ (1 - capRoof U x₀)]
  have htop : capRoof U x₀ + ε < 1 := by
    dsimp [ε]
    linarith [min_le_right δ (1 - capRoof U x₀)]
  have hq : (x₀, capRoof U x₀ + ε) ∈ unitStrip :=
    ⟨by linarith [(hU.inStrip hp).1], htop.le⟩
  have hV := hU.isDownwardCap_insertedCap hq
  have hniche : EqOn
      (partialBarrier (insertedCap U (x₀, capRoof U x₀ + ε)) (Real.pi / 2))
      (partialBarrier U (Real.pi / 2))
      (middleHalfInterval (horizontalLeft U) (horizontalRight U)) := by
    intro x hx
    rw [hV.partialBarrier_pi_div_two, hU.partialBarrier_pi_div_two]
    exact hδworks ε hε.le hεδ htop.le hx
  have hgain : capRoof U x₀ < capRoof (insertedCap U (x₀, capRoof U x₀ + ε)) x₀ := by
    have h := le_capRoof hV.isCompact (inserted_point_mem hq)
    change capRoof U x₀ + ε ≤ _ at h
    linarith
  exact ⟨ε, hε, htop, hU.capScore_lt_of_charged_roof_gain hV
    (hU.subset_insertedCap hq) (hU.horizontalProjection_insertedCap hq hxU)
    hwidth hniche hx₀ hgain⟩

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
  by_contra h
  push_neg at h
  have hwidth : 0 < capWidth U := lt_of_lt_of_le
    (by linarith [one_lt_M] : 0 < M) hU.width_bounds.1
  obtain ⟨ε, hε, htop, hstrict⟩ :=
    hU.isCap.exists_score_improving_insertion hwidth hx₀ hlow h
  have hroof0 := capRoof_nonneg hU.isCap.isCompact
    (fun p hp => (hU.isCap.inStrip hp).1) x₀
  have hp : (x₀, capRoof U x₀ + ε) ∈ unitStrip :=
    ⟨by linarith, htop.le⟩
  exact (not_lt_of_ge (hU.2 _ (hU.isCap.isDownwardCap_insertedCap hp))) hstrict

end AmbidextrousSofa
