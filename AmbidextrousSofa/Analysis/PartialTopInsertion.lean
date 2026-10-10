module

public import AmbidextrousSofa.Analysis.JointCapMaximum
public import AmbidextrousSofa.Analysis.RoofGain

@[expose] public section

/-!
# Top insertion for both orientations at a proper angle

An existing top point on the right protects every first-wall support. An
existing top point on the left protects every second-wall support, while
each changed first wall, including the whole outgoing terminal wall, is
nonpositive on the middle interval. These are two direct set variations.

The whole partial barrier is unchanged on that interval, and the actual
charged roof gains strictly whenever the inserted endpoint was below one.
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
    sweptNiche U α x = sweptNiche V α x := by
  apply le_antisymm
  · apply sweptNiche_le_of_forall hα0 (sweptNiche_nonneg _ _ _)
    intro θ hθ
    calc
      cornerWall U θ x ≤ max (cornerWall U θ x) 0 := le_max_left _ _
      _ = max (cornerWall V θ x) 0 := heq θ hθ
      _ ≤ sweptNiche V α x := max_le
        (cornerWall_le_sweptNiche (sweptWallValues_bddAbove hV hα x) hθ)
        (sweptNiche_nonneg _ _ _)
  · apply sweptNiche_le_of_forall hα0 (sweptNiche_nonneg _ _ _)
    intro θ hθ
    calc
      cornerWall V θ x ≤ max (cornerWall V θ x) 0 := le_max_left _ _
      _ = max (cornerWall U θ x) 0 := (heq θ hθ).symm
      _ ≤ sweptNiche U α x := max_le
        (cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU hα x) hθ)
        (sweptNiche_nonneg _ _ _)

theorem IsDownwardCap.firstWall_inserted_top_of_angle_mem {U : Set Plane}
    (hU : IsDownwardCap U) {a t θ : ℝ} (ht : (t, 1) ∈ U) (hat : a ≤ t)
    (hθ : θ ∈ Icc 0 (Real.pi / 2)) (x : ℝ) :
    firstWall (insertedCap U (a, 1)) θ x = firstWall U θ x := by
  have hp : (a, (1 : ℝ)) ∈ unitStrip := by constructor <;> norm_num
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
    (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hdom : coordDot (a, 1) (unitNormal θ) ≤ support U (unitNormal θ) := by
    have h := coordDot_le_support hU.isCompact ht (unitNormal θ)
    change t * Real.cos θ + 1 * Real.sin θ ≤ _ at h
    change a * Real.cos θ + 1 * Real.sin θ ≤ _
    nlinarith [mul_nonneg (sub_nonneg.mpr hat) hc]
  unfold firstWall
  rw [hU.support_insertedCap_eq_of_dominated hp hs hdom]

theorem IsDownwardCap.secondWall_inserted_top_of_top_left {U : Set Plane}
    (hU : IsDownwardCap U) {a t θ : ℝ} (ht : (t, 1) ∈ U) (hta : t ≤ a)
    (hθ : θ ∈ Icc 0 (Real.pi / 2)) (x : ℝ) :
    secondWall (insertedCap U (a, 1)) θ x = secondWall U θ x := by
  have hp : (a, (1 : ℝ)) ∈ unitStrip := by constructor <;> norm_num
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
    (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hdom : coordDot (a, 1) (companionNormal θ) ≤ support U (companionNormal θ) := by
    have h := coordDot_le_support hU.isCompact ht (companionNormal θ)
    change t * (-Real.sin θ) + 1 * Real.cos θ ≤ _ at h
    change a * (-Real.sin θ) + 1 * Real.cos θ ≤ _
    nlinarith [mul_nonneg (sub_nonneg.mpr hta) hs]
  unfold secondWall
  rw [hU.support_insertedCap_eq_of_dominated hp hc hdom]

theorem IsDownwardCap.clippedCorner_inserted_top_left {U : Set Plane}
    (hU : IsDownwardCap U) {a t θ x : ℝ} (ht : (t, 1) ∈ U) (hta : t ≤ a)
    (hθ : θ ∈ Ioo 0 (Real.pi / 2)) (hax : a ≤ x) :
    max (cornerWall (insertedCap U (a, 1)) θ x) 0 = max (cornerWall U θ x) 0 := by
  have hp : (a, (1 : ℝ)) ∈ unitStrip := by constructor <;> norm_num
  have hV := hU.isDownwardCap_insertedCap hp
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1
    (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  by_cases hdom : coordDot (a, 1) (unitNormal θ) ≤ support U (unitNormal θ)
  · have hfirst : firstWall (insertedCap U (a, 1)) θ x = firstWall U θ x := by
      unfold firstWall
      rw [hU.support_insertedCap_eq_of_dominated hp hs.le hdom]
    rw [cornerWall, cornerWall, hfirst,
      hU.secondWall_inserted_top_of_top_left ht hta ⟨hθ.1.le, hθ.2.le⟩ x]
  · have hnew : support (insertedCap U (a, 1)) (unitNormal θ) =
        coordDot (a, 1) (unitNormal θ) := by
      rw [hU.support_insertedCap hp hs.le, max_eq_right (le_of_not_ge hdom)]
    have hfirst : firstWall (insertedCap U (a, 1)) θ x ≤ 0 := by
      apply (firstWall_le_iff hs).mpr
      rw [hnew]
      change a * Real.cos θ + 1 * Real.sin θ - 1 ≤
        x * Real.cos θ + 0 * Real.sin θ
      nlinarith [Real.sin_le_one θ, mul_nonneg (sub_nonneg.mpr hax) hc.le]
    have hfirstOld : firstWall U θ x ≤ 0 :=
      (firstWall_mono (hU.subset_insertedCap hp) hU.nonempty hV.isCompact hs x).trans hfirst
    rw [max_eq_right ((min_le_left _ _).trans hfirst),
      max_eq_right ((min_le_left _ _).trans hfirstOld)]

/-- Insertion from the right preserves the swept family and the entire
first terminal wall separately. -/
theorem IsDownwardCap.partialBarrier_inserted_top_of_top_right {U : Set Plane}
    (hU : IsDownwardCap U) {a t α x : ℝ} (ht : (t, 1) ∈ U) (hat : a ≤ t)
    (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) (hxa : x ≤ a) :
    partialBarrier (insertedCap U (a, 1)) α x = partialBarrier U α x := by
  have hp : (a, (1 : ℝ)) ∈ unitStrip := by constructor <;> norm_num
  have hsweep : sweptNiche (insertedCap U (a, 1)) α x = sweptNiche U α x :=
    sweptNiche_eq_of_clippedCorner_eq (hU.isDownwardCap_insertedCap hp).isCompact
      hU.isCompact hα0 hα (fun θ hθ =>
        hU.clippedCorner_inserted_top ht hat ⟨hθ.1, hθ.2.trans_le hα⟩ hxa)
  rw [partialBarrier, partialBarrier, hsweep,
    hU.firstWall_inserted_top_of_angle_mem ht hat ⟨hα0.le, hα⟩ x]

/-- Insertion from the left treats a changed whole terminal first wall
explicitly: its new and old heights are both nonpositive on this side. -/
theorem IsDownwardCap.partialBarrier_inserted_top_of_top_left {U : Set Plane}
    (hU : IsDownwardCap U) {a t α x : ℝ} (ht : (t, 1) ∈ U) (hta : t ≤ a)
    (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) (hax : a ≤ x) :
    partialBarrier (insertedCap U (a, 1)) α x = partialBarrier U α x := by
  have hp : (a, (1 : ℝ)) ∈ unitStrip := by constructor <;> norm_num
  have hV := hU.isDownwardCap_insertedCap hp
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0
    (by linarith [hα, Real.pi_pos])
  have hc : 0 ≤ Real.cos α := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos], hα⟩
  have hsweep : sweptNiche (insertedCap U (a, 1)) α x = sweptNiche U α x :=
    sweptNiche_eq_of_clippedCorner_eq hV.isCompact hU.isCompact hα0 hα
      (fun θ hθ => hU.clippedCorner_inserted_top_left ht hta
        ⟨hθ.1, hθ.2.trans_le hα⟩ hax)
  by_cases hdom : coordDot (a, 1) (unitNormal α) ≤ support U (unitNormal α)
  · have hfirst : firstWall (insertedCap U (a, 1)) α x = firstWall U α x := by
      unfold firstWall
      rw [hU.support_insertedCap_eq_of_dominated hp hs.le hdom]
    rw [partialBarrier, partialBarrier, hsweep, hfirst]
  · have hnew : support (insertedCap U (a, 1)) (unitNormal α) =
        coordDot (a, 1) (unitNormal α) := by
      rw [hU.support_insertedCap hp hs.le, max_eq_right (le_of_not_ge hdom)]
    have hfirst : firstWall (insertedCap U (a, 1)) α x ≤ 0 := by
      apply (firstWall_le_iff hs).mpr
      rw [hnew]
      change a * Real.cos α + 1 * Real.sin α - 1 ≤
        x * Real.cos α + 0 * Real.sin α
      nlinarith [Real.sin_le_one α, mul_nonneg (sub_nonneg.mpr hax) hc]
    have hfirstOld : firstWall U α x ≤ 0 :=
      (firstWall_mono (hU.subset_insertedCap hp) hU.nonempty hV.isCompact hs x).trans hfirst
    rw [partialBarrier, partialBarrier, hsweep,
      max_eq_left (hfirst.trans (sweptNiche_nonneg U α x)),
      max_eq_left (hfirstOld.trans (sweptNiche_nonneg U α x))]

theorem IsJointCapMaximizer.middle_right_eq_one_of_top_right
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α) {t : ℝ}
    (ht : (t, 1) ∈ U) (htRight : horizontalRight U - capWidth U / 4 ≤ t) :
    capRoof U (horizontalRight U - capWidth U / 4) = 1 := by
  let b := horizontalRight U - capWidth U / 4
  have hw : 0 < capWidth U := by linarith [hU.width_bounds.1, one_lt_M]
  have hb : b ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex]
    dsimp [b]
    unfold capWidth at *
    constructor <;> linarith
  have hp : (b, (1 : ℝ)) ∈ unitStrip := by constructor <;> norm_num
  have hV := hU.isCap.isDownwardCap_insertedCap hp
  apply le_antisymm (capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _)
  by_contra h
  have hgain : capRoof U b < capRoof (insertedCap U (b, 1)) b := by
    rw [hU.isCap.capRoof_inserted_one]
    exact lt_of_not_ge h
  have hstrict := hU.isCap.capScore_lt_of_charged_roof_gain hV
    (hU.isCap.subset_insertedCap hp) (hU.isCap.horizontalProjection_insertedCap hp hb) hw
    (α := α) (x₀ := b)
    (fun x hx => hU.isCap.partialBarrier_inserted_top_of_top_right ht htRight
      hU.angle_pos hU.angle_mem.2 hx.2)
    (Or.inr ⟨le_rfl, by dsimp [b]; linarith⟩) hgain
  exact (not_lt_of_ge (hU.score_le_same_angle hV)) hstrict

theorem IsJointCapMaximizer.middle_left_eq_one_of_top_left
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α) {t : ℝ}
    (ht : (t, 1) ∈ U) (htLeft : t ≤ horizontalLeft U + capWidth U / 4) :
    capRoof U (horizontalLeft U + capWidth U / 4) = 1 := by
  let a := horizontalLeft U + capWidth U / 4
  have hw : 0 < capWidth U := by linarith [hU.width_bounds.1, one_lt_M]
  have ha : a ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex]
    dsimp [a]
    unfold capWidth at *
    constructor <;> linarith
  have hp : (a, (1 : ℝ)) ∈ unitStrip := by constructor <;> norm_num
  have hV := hU.isCap.isDownwardCap_insertedCap hp
  apply le_antisymm (capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _)
  by_contra h
  have hgain : capRoof U a < capRoof (insertedCap U (a, 1)) a := by
    rw [hU.isCap.capRoof_inserted_one]
    exact lt_of_not_ge h
  have hstrict := hU.isCap.capScore_lt_of_charged_roof_gain hV
    (hU.isCap.subset_insertedCap hp) (hU.isCap.horizontalProjection_insertedCap hp ha) hw
    (α := α) (x₀ := a)
    (fun x hx => hU.isCap.partialBarrier_inserted_top_of_top_left ht htLeft
      hU.angle_pos hU.angle_mem.2 hx.1)
    (Or.inl ⟨by dsimp [a]; linarith, le_rfl⟩) hgain
  exact (not_lt_of_ge (hU.score_le_same_angle hV)) hstrict

/-- Height attainment plus the two literal insertions puts an actual top
point inside the middle interval at any height-one joint maximum. -/
theorem IsJointCapMaximizer.top_meets_middle {U : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) (hheight : capHeight U = 1) :
    ∃ t ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), (t, 1) ∈ U := by
  let a := horizontalLeft U + capWidth U / 4
  let b := horizontalRight U - capWidth U / 4
  have hw : 0 < capWidth U := by linarith [hU.width_bounds.1, one_lt_M]
  have hab : a ≤ b := by dsimp [a, b]; unfold capWidth at *; linarith
  have ha : a ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex]
    dsimp [a]
    unfold capWidth at *
    constructor <;> linarith
  have hb : b ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex]
    dsimp [b]
    unfold capWidth at *
    constructor <;> linarith
  obtain ⟨q, hq, hqH⟩ := exists_coordDot_eq_support
    hU.isCap.isCompact hU.isCap.nonempty (0, 1)
  have hqone : q.2 = 1 := by
    change q.1 * 0 + q.2 * 1 = capHeight U at hqH
    simpa only [mul_zero, mul_one, zero_add, hheight] using hqH
  have htop : (q.1, 1) ∈ U := by simpa only [← hqone, Prod.mk.eta] using hq
  by_cases hqa : q.1 ≤ a
  · refine ⟨a, ⟨le_rfl, hab⟩, ?_⟩
    have hroof := capRoof_mem hU.isCap.isCompact ha
    rwa [hU.middle_left_eq_one_of_top_left htop hqa] at hroof
  by_cases hbq : b ≤ q.1
  · refine ⟨b, ⟨hab, le_rfl⟩, ?_⟩
    have hroof := capRoof_mem hU.isCap.isCompact hb
    rwa [hU.middle_right_eq_one_of_top_right htop hbq] at hroof
  · exact ⟨q.1, ⟨le_of_not_ge hqa, le_of_not_ge hbq⟩, htop⟩

theorem IsJointCapMaximizer.middle_right_eq_one_of_affine_nonneg
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hheight : capHeight U = 1) {m c : ℝ} (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    capRoof U (horizontalRight U - capWidth U / 4) = 1 := by
  obtain ⟨t, ht, htop⟩ := hU.top_meets_middle hheight
  have hw : 0 < capWidth U := by linarith [hU.width_bounds.1, one_lt_M]
  have hab : horizontalLeft U + capWidth U / 4 ≤ horizontalRight U - capWidth U / 4 := by
    unfold capWidth at *
    linarith
  have hb := haffine (horizontalRight U - capWidth U / 4) ⟨hab, le_rfl⟩
  have htline := haffine t ht
  have htone : 1 ≤ capRoof U t := le_capRoof hU.isCap.isCompact htop
  apply le_antisymm (capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _)
  have htb : t ≤ horizontalRight U - capWidth U / 4 := ht.2
  have hmul := mul_nonneg hm (sub_nonneg.mpr htb)
  nlinarith

theorem IsJointCapMaximizer.middle_left_eq_one_of_affine_nonpos
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hheight : capHeight U = 1) {m c : ℝ} (hm : m ≤ 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    capRoof U (horizontalLeft U + capWidth U / 4) = 1 := by
  obtain ⟨t, ht, htop⟩ := hU.top_meets_middle hheight
  have hw : 0 < capWidth U := by linarith [hU.width_bounds.1, one_lt_M]
  have hab : horizontalLeft U + capWidth U / 4 ≤ horizontalRight U - capWidth U / 4 := by
    unfold capWidth at *
    linarith
  have ha := haffine (horizontalLeft U + capWidth U / 4) ⟨le_rfl, hab⟩
  have htline := haffine t ht
  have htone : 1 ≤ capRoof U t := le_capRoof hU.isCap.isCompact htop
  apply le_antisymm (capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _)
  have hat : horizontalLeft U + capWidth U / 4 ≤ t := ht.1
  have hmul := mul_nonneg (neg_nonneg.mpr hm) (sub_nonneg.mpr hat)
  nlinarith

end AmbidextrousSofa
