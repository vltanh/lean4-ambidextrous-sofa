module

public import AmbidextrousSofa.Analysis.RoofGain

@[expose] public section

/-!
# Actual point insertion in inactive supporting directions

The maximum baseline wall slack on an interval is attained at one of its
two endpoints. If every supporting direction of an actual roof point has
strictly negative middle slack, compactness of the entire upper semicircle
gives a uniform insertion radius. Each changed support then has a wall that
excludes the whole positive-height forbidden quadrant on the middle. This
controls both the visited two-wall corners and the whole terminal first wall
of the partial barrier, at every angle up to a full turn.

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
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter hθ
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

/-- The inactivity alternative controls the visited corners and the genuine outgoing
first wall, including at the full-angle endpoint. -/
theorem partialBarrier_eq_of_support_eq_or_inactive {U V : Set Plane}
    (hU : IsDownwardCap U) (hV : IsDownwardCap V) (hUV : U ⊆ V)
    {α x : ℝ} (hα0 : 0 < α) (hαL : α ≤ Real.pi / 2)
    (hwalls : ∀ θ ∈ Ioo 0 Real.pi,
      support V (unitNormal θ) = support U (unitNormal θ) ∨
        support V (unitNormal θ) - 1 ≤ coordDot (x, 0) (unitNormal θ)) :
    partialBarrier V α x = partialBarrier U α x := by
  have hn : sweptNiche V α x = sweptNiche U α x := by
    refine le_antisymm (sweptNiche_le_of_forall hα0 (sweptNiche_nonneg U α x) fun θ hθ => ?_)
      (sweptNiche_mono hUV hU.nonempty hV.isCompact hα0 hαL x)
    have hsecond := hwalls (θ + Real.pi / 2) ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
    rw [← companionNormal_eq_unitNormal] at hsecond
    exact (le_max_left _ _).trans <| (clippedCorner_eq_of_support_eq_or_inactive hU hV hUV
      ⟨hθ.1, hθ.2.trans_le hαL⟩ (hwalls θ ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩)
        hsecond).trans_le <| max_le (cornerWall_le_sweptNiche
          (sweptWallValues_bddAbove hU.isCompact hαL x) hθ) (sweptNiche_nonneg U α x)
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [Real.pi_pos])
  rcases hwalls α ⟨hα0, by linarith [Real.pi_pos]⟩ with hsame | hinactive
  · simp only [partialBarrier, hn, firstWall, hsame]
  · have hV0 := (firstWall_le_iff hs).mpr hinactive
    rw [partialBarrier, partialBarrier, hn, max_eq_left (hV0.trans (sweptNiche_nonneg U α x)),
      max_eq_left (((firstWall_mono hUV hU.nonempty hV.isCompact hs x).trans hV0).trans
        (sweptNiche_nonneg U α x))]

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
  obtain ⟨δ, hδ, hbound⟩ := isCompact_Icc.exists_forall_le' (a := 0)
    (f := fun θ => max (angleSupport U θ - coordDot p (unitNormal θ)) (-middleWallSlack U a b θ))
    (((continuous_angleSupport hU.isCompact).sub ((continuous_coordDot_left p).comp
      continuous_unitNormal)).max (continuous_middleWallSlack hU.isCompact a b).neg).continuousOn
    fun θ hθ => by
      by_contra! h
      have := hinactive θ hθ (le_antisymm (coordDot_le_support hU.isCompact hp _)
        (by linarith [(max_le_iff.mp h).1]))
      linarith [(max_le_iff.mp h).2]
  refine ⟨δ, hδ, fun ε hε hεδ htop x hx θ hθ => ?_⟩
  have hq : (p.1, p.2 + ε) ∈ unitStrip := ⟨by linarith [(hU.inStrip hp).1], htop⟩
  have hsin := mul_le_of_le_one_right hε (Real.sin_le_one θ)
  have hpS := coordDot_le_support hU.isCompact hp (unitNormal θ)
  have hslack := baseline_slack_le_middleWallSlack U hx θ
  have hb := hbound θ (Ioo_subset_Icc_self hθ)
  rw [hU.support_insertedCap hq (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).le]
  simp only [angleSupport, coordDot, unitNormal] at hb hslack hpS ⊢
  rcases le_max_iff.mp hb with h | h
  · exact .inl (max_eq_left (by linarith))
  · exact .inr (sub_le_iff_le_add.mpr (max_le (by linarith) (by linarith)))

/-- A charged roof point below height one of a cap maximizing the score at a fixed angle has a
supporting normal whose middle wall is not strictly inactive: otherwise the point could be
raised while keeping the whole partial barrier on the middle, which would strictly increase the
score. -/
theorem IsDownwardCap.exists_noninactive_normal_on_wing {U : Set Plane} (hU : IsDownwardCap U)
    {α : ℝ} (hα0 : 0 < α) (hα : α ≤ Real.pi / 2)
    (hmax : ∀ V, IsDownwardCap V → capScore V α ≤ capScore U α) (hwidth : 0 < capWidth U)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Icc (horizontalLeft U) (horizontalLeft U + capWidth U / 4) ∪
      Icc (horizontalRight U - capWidth U / 4) (horizontalRight U))
    (hlow : capRoof U x₀ < 1) :
    ∃ θ ∈ Icc 0 Real.pi,
      coordDot (x₀, capRoof U x₀) (unitNormal θ) = angleSupport U θ ∧
      0 ≤ middleWallSlack U (horizontalLeft U + capWidth U / 4)
        (horizontalRight U - capWidth U / 4) θ := by
  by_contra! h
  have hxU : x₀ ∈ horizontalProjection U := by
    rw [hU.horizontalProjection_eq_Icc]
    unfold capWidth at hwidth hx₀
    rcases hx₀ with hx₀ | hx₀ <;> constructor <;> linarith [hx₀.1, hx₀.2]
  have hp := capRoof_mem hU.isCompact hxU
  obtain ⟨δ, hδ, hδworks⟩ := hU.exists_inactive_support_insertion_radius hp h
  obtain ⟨ε, hε, hεδ⟩ := exists_between (lt_min hδ (sub_pos.2 hlow))
  rw [lt_min_iff] at hεδ
  have hq : (x₀, capRoof U x₀ + ε) ∈ unitStrip := ⟨by linarith [(hU.inStrip hp).1], by linarith⟩
  have hV := hU.isDownwardCap_insertedCap hq
  exact (hmax _ hV).not_gt <| hU.capScore_lt_of_charged_roof_gain hV
    (hU.subset_insertedCap hq) (hU.horizontalProjection_insertedCap hq hxU) hwidth
    (fun x hx => partialBarrier_eq_of_support_eq_or_inactive hU hV (hU.subset_insertedCap hq)
      hα0 hα (hδworks ε hε.le hεδ.1 hq.2 x hx)) hx₀
    ((lt_add_of_pos_right _ hε).trans_le (le_capRoof hV.isCompact (inserted_point_mem hq)))

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
        (horizontalRight U - capWidth U / 4) θ :=
  hU.isCap.exists_noninactive_normal_on_wing (by positivity) le_rfl hU.2
    (by linarith [hU.width_bounds.1, one_lt_M]) hx₀ hlow

end AmbidextrousSofa
