import AmbidextrousSofa.Analysis.InactiveNormals
import AmbidextrousSofa.Analysis.JointCapMaximum

/-!
# Inactive-normal insertion for the actual partial barrier

Each upper support that changes under the insertion either keeps its old
value or has nonpositive inner-wall height throughout the middle window.
This controls both the visited two-wall corners and the whole terminal
first wall. The resulting literal cap variation gives a supporting-normal
necessary condition at every charged roof point of a joint maximizer.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem sweptNiche_partial_eq_of_support_eq_or_inactive {U V : Set Plane}
    (hU : IsDownwardCap U) (hV : IsDownwardCap V) (hUV : U ⊆ V)
    {α x : ℝ} (hα0 : 0 < α) (hαL : α ≤ Real.pi / 2)
    (hwalls : ∀ θ ∈ Ioo 0 Real.pi,
      support V (unitNormal θ) = support U (unitNormal θ) ∨
        support V (unitNormal θ) - 1 ≤ coordDot (x, 0) (unitNormal θ)) :
    sweptNiche V α x = sweptNiche U α x := by
  apply le_antisymm
  · apply sweptNiche_le_of_forall hα0 (sweptNiche_nonneg U α x)
    intro θ hθ
    have hθL : θ < Real.pi / 2 := hθ.2.trans_le hαL
    have hfirst := hwalls θ ⟨hθ.1, by linarith [Real.pi_pos]⟩
    have hsecond := hwalls (θ + Real.pi / 2)
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith⟩
    rw [← companionNormal_eq_unitNormal θ] at hsecond
    calc
      cornerWall V θ x ≤ max (cornerWall V θ x) 0 := le_max_left _ _
      _ = max (cornerWall U θ x) 0 :=
        clippedCorner_eq_of_support_eq_or_inactive hU hV hUV ⟨hθ.1, hθL⟩ hfirst hsecond
      _ ≤ sweptNiche U α x := max_le
        (cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCompact hαL x) hθ)
        (sweptNiche_nonneg U α x)
  · exact sweptNiche_mono hUV hU.nonempty hV.isCompact hα0 hαL x

/-- The same inactivity alternative also controls the genuine outgoing
first wall, including at the full-angle endpoint. -/
theorem partialBarrier_eq_of_support_eq_or_inactive {U V : Set Plane}
    (hU : IsDownwardCap U) (hV : IsDownwardCap V) (hUV : U ⊆ V)
    {α x : ℝ} (hα0 : 0 < α) (hαL : α ≤ Real.pi / 2)
    (hwalls : ∀ θ ∈ Ioo 0 Real.pi,
      support V (unitNormal θ) = support U (unitNormal θ) ∨
        support V (unitNormal θ) - 1 ≤ coordDot (x, 0) (unitNormal θ)) :
    partialBarrier V α x = partialBarrier U α x := by
  have hn := sweptNiche_partial_eq_of_support_eq_or_inactive hU hV hUV hα0 hαL hwalls
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0
    (by linarith [Real.pi_pos])
  rcases hwalls α ⟨hα0, by linarith [Real.pi_pos]⟩ with hsame | hinactive
  · simp only [partialBarrier, hn, firstWall, hsame]
  · have hVzero : firstWall V α x ≤ 0 := (firstWall_le_iff hs).mpr hinactive
    have hUzero : firstWall U α x ≤ 0 :=
      (firstWall_mono hUV hU.nonempty hV.isCompact hs x).trans hVzero
    rw [partialBarrier, partialBarrier, hn,
      max_eq_left (hVzero.trans (sweptNiche_nonneg U α x)),
      max_eq_left (hUzero.trans (sweptNiche_nonneg U α x))]

/-- A uniform radius for the complete support alternatives. The maximum
of the support gap and the negative wall slack is positive on the compact
upper semicircle, so the choice does not depend on a contact angle. -/
theorem IsDownwardCap.exists_inactive_support_insertion_radius {U : Set Plane}
    (hU : IsDownwardCap U) {p : Plane} (hp : p ∈ U) {a b : ℝ}
    (hinactive : ∀ θ ∈ Icc 0 Real.pi,
      coordDot p (unitNormal θ) = angleSupport U θ → middleWallSlack U a b θ < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < δ → p.2 + ε ≤ 1 →
      ∀ x ∈ Icc a b, ∀ θ ∈ Ioo 0 Real.pi,
        support (insertedCap U (p.1, p.2 + ε)) (unitNormal θ) = support U (unitNormal θ) ∨
          support (insertedCap U (p.1, p.2 + ε)) (unitNormal θ) - 1 ≤
            coordDot (x, 0) (unitNormal θ) := by
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
  intro ε hε hεδ htop x hx θ hθ
  let q : Plane := (p.1, p.2 + ε)
  have hq : q ∈ unitStrip := ⟨by dsimp [q]; linarith [(hU.inStrip hp).1], htop⟩
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

theorem IsDownwardCap.exists_inactive_partial_insertion_radius {U : Set Plane}
    (hU : IsDownwardCap U) {p : Plane} (hp : p ∈ U) {a b α : ℝ}
    (hα0 : 0 < α) (hαL : α ≤ Real.pi / 2)
    (hinactive : ∀ θ ∈ Icc 0 Real.pi,
      coordDot p (unitNormal θ) = angleSupport U θ → middleWallSlack U a b θ < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < δ → p.2 + ε ≤ 1 →
      EqOn (partialBarrier (insertedCap U (p.1, p.2 + ε)) α)
        (partialBarrier U α) (Icc a b) := by
  obtain ⟨δ, hδ, hδworks⟩ := hU.exists_inactive_support_insertion_radius hp hinactive
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ htop x hx
  have hq : (p.1, p.2 + ε) ∈ unitStrip :=
    ⟨by linarith [(hU.inStrip hp).1], htop⟩
  exact partialBarrier_eq_of_support_eq_or_inactive hU (hU.isDownwardCap_insertedCap hq)
    (hU.subset_insertedCap hq) hα0 hαL (hδworks ε hε hεδ htop x hx)

/-- An actual charged roof point can be raised while preserving the
whole fixed-angle partial barrier when all its supporting walls are
strictly inactive on the middle. -/
theorem IsDownwardCap.exists_partial_score_improving_insertion {U : Set Plane}
    (hU : IsDownwardCap U) (hwidth : 0 < capWidth U) {α x₀ : ℝ}
    (hα0 : 0 < α) (hαL : α ≤ Real.pi / 2)
    (hx₀ : x₀ ∈ Icc (horizontalLeft U)
        (horizontalLeft U + capWidth U / 4) ∪
      Icc (horizontalRight U - capWidth U / 4) (horizontalRight U))
    (hlow : capRoof U x₀ < 1)
    (hinactive : ∀ θ ∈ Icc 0 Real.pi,
      coordDot (x₀, capRoof U x₀) (unitNormal θ) = angleSupport U θ →
      middleWallSlack U (horizontalLeft U + capWidth U / 4)
        (horizontalRight U - capWidth U / 4) θ < 0) :
    ∃ ε : ℝ, 0 < ε ∧ capRoof U x₀ + ε < 1 ∧
      capScore U α < capScore (insertedCap U (x₀, capRoof U x₀ + ε)) α := by
  have hxU : x₀ ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
    unfold capWidth at hwidth hx₀
    rcases hx₀ with hx₀ | hx₀ <;> constructor <;> linarith [hx₀.1, hx₀.2]
  have hp := capRoof_mem hU.isCompact hxU
  obtain ⟨δ, hδ, hδworks⟩ :=
    hU.exists_inactive_partial_insertion_radius hp hα0 hαL hinactive
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
  have hniche : EqOn (partialBarrier (insertedCap U (x₀, capRoof U x₀ + ε)) α)
      (partialBarrier U α) (middleHalfInterval (horizontalLeft U) (horizontalRight U)) :=
    hδworks ε hε.le hεδ htop.le
  have hgain : capRoof U x₀ < capRoof (insertedCap U (x₀, capRoof U x₀ + ε)) x₀ := by
    have h := le_capRoof hV.isCompact (inserted_point_mem hq)
    change capRoof U x₀ + ε ≤ _ at h
    linarith
  exact ⟨ε, hε, htop, hU.capScore_lt_of_charged_roof_gain hV
    (hU.subset_insertedCap hq) (hU.horizontalProjection_insertedCap hq hxU)
    hwidth hniche hx₀ hgain⟩

theorem IsJointCapMaximizer.exists_noninactive_normal_on_wing {U : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) {x₀ : ℝ}
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
  obtain ⟨ε, hε, htop, hstrict⟩ := hU.isCap.exists_partial_score_improving_insertion
    hwidth hU.angle_pos hU.angle_mem.2 hx₀ hlow h
  have hroof0 := capRoof_nonneg hU.isCap.isCompact
    (fun p hp => (hU.isCap.inStrip hp).1) x₀
  have hp : (x₀, capRoof U x₀ + ε) ∈ unitStrip :=
    ⟨by linarith, htop.le⟩
  exact (not_lt_of_ge (hU.score_le_same_angle (hU.isCap.isDownwardCap_insertedCap hp))) hstrict

end AmbidextrousSofa
