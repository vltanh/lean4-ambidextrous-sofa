module

public import AmbidextrousSofa.Analysis.InactiveNormals
public import AmbidextrousSofa.Analysis.JointCapMaximum

@[expose] public section

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

/-- A charged roof point below height one has a supporting normal whose middle wall is not
strictly inactive: otherwise the point could be raised while keeping the whole fixed-angle
partial barrier on the middle, which would strictly increase the score. -/
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
  by_contra! h
  have hC := hU.isCap
  have hwidth : 0 < capWidth U := by linarith [one_lt_M, hU.width_bounds.1]
  have hxU : x₀ ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hC.nonempty hC.isCompact hC.convex]
    unfold capWidth at hwidth hx₀
    rcases hx₀ with hx₀ | hx₀ <;> constructor <;> linarith [hx₀.1, hx₀.2]
  have hp := capRoof_mem hC.isCompact hxU
  obtain ⟨δ, hδ, hδworks⟩ := hC.exists_inactive_support_insertion_radius hp h
  obtain ⟨ε, hε, hεδ⟩ := exists_between (lt_min hδ (sub_pos.2 hlow))
  rw [lt_min_iff] at hεδ
  have hq : (x₀, capRoof U x₀ + ε) ∈ unitStrip := ⟨by linarith [(hC.inStrip hp).1], by linarith⟩
  have hV := hC.isDownwardCap_insertedCap hq
  exact (hU.score_le_same_angle hV).not_gt <| hC.capScore_lt_of_charged_roof_gain hV
    (hC.subset_insertedCap hq) (hC.horizontalProjection_insertedCap hq hxU) hwidth
    (fun x hx => partialBarrier_eq_of_support_eq_or_inactive hC hV (hC.subset_insertedCap hq)
      hU.angle_pos hU.angle_mem.2 (hδworks ε hε.le hεδ.1 hq.2 x hx)) hx₀
    ((lt_add_of_pos_right _ hε).trans_le (le_capRoof hV.isCompact (inserted_point_mem hq)))

end AmbidextrousSofa
