module

public import AmbidextrousSofa.Analysis.JointCapMaximum
public import AmbidextrousSofa.Analysis.RoofGain

@[expose] public section

/-!
# Top insertion for both orientations at a proper angle

An existing top point on the left protects every second-wall support, while
each changed first wall, including the whole outgoing terminal wall, is
nonpositive on the middle interval. Together with the insertion from the
right, these are two direct set variations.

In both the whole partial barrier is unchanged on that interval, and the
actual charged roof gains strictly whenever the inserted endpoint was below one.
Thus a height-one joint maximum has a top point in its middle interval.
The high endpoint of any affine middle roof is consequently at height one,
for either sign of its slope.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem sweptNiche_eq_of_clippedCorner_eq {U V : Set Plane}
    (hU : IsCompact U) (hV : IsCompact V) {α x : ℝ}
    (hα0 : 0 < α) (hα : α ≤ Real.pi / 2)
    (heq : ∀ θ ∈ Ioo 0 α, max (cornerWall U θ x) 0 = max (cornerWall V θ x) 0) :
    sweptNiche U α x = sweptNiche V α x :=
  le_antisymm (sweptNiche_le_of_clippedCorner_le hV hα0 hα fun θ hθ => (heq θ hθ).le)
    (sweptNiche_le_of_clippedCorner_le hU hα0 hα fun θ hθ => (heq θ hθ).ge)

/-- A first wall changed by a top insertion left of `x` is nonpositive at `x`, before and
after the insertion. -/
private theorem IsDownwardCap.firstWall_inserted_top_left {U : Set Plane} (hU : IsDownwardCap U)
    {a θ x : ℝ} (hs : 0 < Real.sin θ) (hc : 0 ≤ Real.cos θ) (hax : a ≤ x) :
    firstWall (insertedCap U (a, 1)) θ x = firstWall U θ x ∨
      firstWall (insertedCap U (a, 1)) θ x ≤ 0 ∧ firstWall U θ x ≤ 0 := by
  have hp : (a, (1 : ℝ)) ∈ unitStrip := ⟨zero_le_one, le_rfl⟩
  by_cases hdom : coordDot (a, 1) (unitNormal θ) ≤ support U (unitNormal θ)
  · exact .inl (by rw [firstWall, firstWall, hU.support_insertedCap_eq_of_dominated hp hs.le hdom])
  have hfirst : firstWall (insertedCap U (a, 1)) θ x ≤ 0 := by
    rw [firstWall_le_iff hs, hU.support_insertedCap hp hs.le, max_eq_right (le_of_not_ge hdom)]
    simp only [coordDot, unitNormal]
    linarith [Real.sin_le_one θ, mul_nonneg (sub_nonneg.mpr hax) hc]
  exact .inr ⟨hfirst, (firstWall_mono (hU.subset_insertedCap hp) hU.nonempty
    (hU.isDownwardCap_insertedCap hp).isCompact hs x).trans hfirst⟩

/-- Insertion from the left treats a changed whole terminal first wall
explicitly: its new and old heights are both nonpositive on this side. -/
theorem IsDownwardCap.partialBarrier_inserted_top_of_top_left {U : Set Plane}
    (hU : IsDownwardCap U) {a t α x : ℝ} (ht : (t, 1) ∈ U) (hta : t ≤ a)
    (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) (hax : a ≤ x) :
    partialBarrier (insertedCap U (a, 1)) α x = partialBarrier U α x := by
  have hp : (a, (1 : ℝ)) ∈ unitStrip := ⟨zero_le_one, le_rfl⟩
  have hsweep : sweptNiche (insertedCap U (a, 1)) α x = sweptNiche U α x :=
    sweptNiche_eq_of_clippedCorner_eq (hU.isDownwardCap_insertedCap hp).isCompact hU.isCompact
      hα0 hα fun θ hθ => by
        have hθL := hθ.2.trans_le hα
        have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [Real.pi_pos])
        have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθL⟩
        rcases hU.firstWall_inserted_top_left hs hc.le hax with h | ⟨h1, h2⟩
        · rw [cornerWall, cornerWall, h, secondWall, secondWall,
            hU.support_insertedCap_eq_of_dominated hp hc.le (le_trans (by
              simp only [coordDot, companionNormal]
              linarith [mul_nonneg (sub_nonneg.mpr hta) hs.le])
              (coordDot_le_support hU.isCompact ht _))]
        · rw [cornerWall, cornerWall, max_eq_right ((min_le_left _ _).trans h1),
            max_eq_right ((min_le_left _ _).trans h2)]
  rcases hU.firstWall_inserted_top_left
    (Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [Real.pi_pos]))
    (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hα⟩) hax with h | ⟨h1, h2⟩
  · rw [partialBarrier, partialBarrier, hsweep, h]
  · rw [partialBarrier, partialBarrier, hsweep, max_eq_left (h1.trans (sweptNiche_nonneg U α x)),
      max_eq_left (h2.trans (sweptNiche_nonneg U α x))]

/-- A charged wing point whose top insertion keeps the whole partial barrier on the middle
is already a top point of a joint maximizer. -/
private theorem IsJointCapMaximizer.top_mem_of_insertion {U : Set Plane} {α b : ℝ}
    (hU : IsJointCapMaximizer U α)
    (hb : b ∈ Icc (horizontalLeft U) (horizontalLeft U + capWidth U / 4) ∪
      Icc (horizontalRight U - capWidth U / 4) (horizontalRight U))
    (hbar : EqOn (partialBarrier (insertedCap U (b, 1)) α) (partialBarrier U α)
      (middleHalfInterval (horizontalLeft U) (horizontalRight U))) :
    (b, 1) ∈ U := by
  have hC := hU.isCap
  have hp : (b, (1 : ℝ)) ∈ unitStrip := ⟨zero_le_one, le_rfl⟩
  have hw : 0 < capWidth U := by linarith [hU.width_bounds.1, one_lt_M]
  have hbU : b ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hC.nonempty hC.isCompact hC.convex]
    unfold capWidth at hw hb
    rcases hb with hb | hb <;> constructor <;> linarith [hb.1, hb.2]
  have hV := hC.isDownwardCap_insertedCap hp
  have h1 : capRoof U b = 1 := le_antisymm (capRoof_le_one hC.isCompact hC.inStrip _) <|
    not_lt.1 fun h => (hU.score_le_same_angle hV).not_gt <| hC.capScore_lt_of_charged_roof_gain hV
      (hC.subset_insertedCap hp) (hC.horizontalProjection_insertedCap hp hbU) hw hbar hb
      (by rwa [hC.capRoof_inserted_one])
  simpa only [h1] using capRoof_mem hC.isCompact hbU

/-- Height attainment plus the two literal insertions puts an actual top
point inside the middle interval at any height-one joint maximum. -/
theorem IsJointCapMaximizer.top_meets_middle {U : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) (hheight : capHeight U = 1) :
    ∃ t ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), (t, 1) ∈ U := by
  have hw : 0 < capWidth U := by linarith [hU.width_bounds.1, one_lt_M]
  have hab : horizontalLeft U + capWidth U / 4 ≤ horizontalRight U - capWidth U / 4 := by
    unfold capWidth at *; linarith
  obtain ⟨q, hq, hqH⟩ := exists_coordDot_eq_support hU.isCap.isCompact hU.isCap.nonempty (0, 1)
  have hqone : q.2 = 1 := by
    change q.1 * 0 + q.2 * 1 = capHeight U at hqH
    simpa only [mul_zero, mul_one, zero_add, hheight] using hqH
  have htop : (q.1, 1) ∈ U := by simpa only [← hqone, Prod.mk.eta] using hq
  by_cases hqa : q.1 ≤ horizontalLeft U + capWidth U / 4
  · exact ⟨horizontalLeft U + capWidth U / 4, ⟨le_rfl, hab⟩, hU.top_mem_of_insertion
      (.inl ⟨by linarith, le_rfl⟩) fun _ hx => hU.isCap.partialBarrier_inserted_top_of_top_left
        htop hqa hU.angle_pos hU.angle_mem.2 hx.1⟩
  by_cases hbq : horizontalRight U - capWidth U / 4 ≤ q.1
  · exact ⟨horizontalRight U - capWidth U / 4, ⟨hab, le_rfl⟩, hU.top_mem_of_insertion
      (.inr ⟨le_rfl, by linarith⟩) fun _ hx => hU.isCap.partialBarrier_inserted_top_of_top_right
        htop hbq hU.angle_pos hU.angle_mem.2 hx.2⟩
  exact ⟨q.1, ⟨le_of_not_ge hqa, le_of_not_ge hbq⟩, htop⟩

theorem IsJointCapMaximizer.middle_right_eq_one_of_affine_nonneg
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hheight : capHeight U = 1) {m c : ℝ} (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    capRoof U (horizontalRight U - capWidth U / 4) = 1 := by
  obtain ⟨t, ht, htop⟩ := hU.top_meets_middle hheight
  have htb : t ≤ horizontalRight U - capWidth U / 4 := ht.2
  linarith [haffine (horizontalRight U - capWidth U / 4) ⟨ht.1.trans ht.2, le_rfl⟩,
    haffine t ht, capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip
      (horizontalRight U - capWidth U / 4),
    le_capRoof hU.isCap.isCompact htop, mul_nonneg hm (sub_nonneg.mpr htb)]

theorem IsJointCapMaximizer.middle_left_eq_one_of_affine_nonpos
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hheight : capHeight U = 1) {m c : ℝ} (hm : m ≤ 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    capRoof U (horizontalLeft U + capWidth U / 4) = 1 := by
  obtain ⟨t, ht, htop⟩ := hU.top_meets_middle hheight
  have hat : horizontalLeft U + capWidth U / 4 ≤ t := ht.1
  linarith [haffine (horizontalLeft U + capWidth U / 4) ⟨le_rfl, ht.1.trans ht.2⟩, haffine t ht,
    capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip (horizontalLeft U + capWidth U / 4),
    le_capRoof hU.isCap.isCompact htop, mul_nonneg (neg_nonneg.mpr hm) (sub_nonneg.mpr hat)]

end AmbidextrousSofa
