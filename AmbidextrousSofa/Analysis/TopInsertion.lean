import AmbidextrousSofa.Analysis.CapInsertion
import AmbidextrousSofa.Analysis.GlobalCapMaximum
import AmbidextrousSofa.Analysis.FiniteScore

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

theorem IsDownwardCap.firstWall_inserted_top {U : Set Plane}
    (hU : IsDownwardCap U) {a t θ : ℝ} (ht : (t, 1) ∈ U) (hat : a ≤ t)
    (hθ : θ ∈ Ioo 0 (Real.pi / 2)) (x : ℝ) :
    firstWall (insertedCap U (a, 1)) θ x = firstWall U θ x := by
  have hp : (a, (1 : ℝ)) ∈ unitStrip := by constructor <;> norm_num
  have hs : 0 ≤ Real.sin θ := (Real.sin_pos_of_pos_of_lt_pi hθ.1
    (by linarith [hθ.2, Real.pi_pos])).le
  have hc : 0 ≤ Real.cos θ := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩).le
  have hdom : coordDot (a, 1) (unitNormal θ) ≤ support U (unitNormal θ) := by
    have h := coordDot_le_support hU.isCompact ht (unitNormal θ)
    change t * Real.cos θ + 1 * Real.sin θ ≤ _ at h
    change a * Real.cos θ + 1 * Real.sin θ ≤ _
    nlinarith [mul_nonneg (sub_nonneg.mpr hat) hc]
  unfold firstWall
  rw [hU.support_insertedCap_eq_of_dominated hp hs hdom]

theorem IsDownwardCap.clippedCorner_inserted_top {U : Set Plane}
    (hU : IsDownwardCap U) {a t θ x : ℝ} (ht : (t, 1) ∈ U) (hat : a ≤ t)
    (hθ : θ ∈ Ioo 0 (Real.pi / 2)) (hxa : x ≤ a) :
    max (cornerWall (insertedCap U (a, 1)) θ x) 0 =
      max (cornerWall U θ x) 0 := by
  have hp : (a, (1 : ℝ)) ∈ unitStrip := by constructor <;> norm_num
  have hV := hU.isDownwardCap_insertedCap hp
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1
    (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  by_cases hdom : coordDot (a, 1) (companionNormal θ) ≤ support U (companionNormal θ)
  · have hsecond : secondWall (insertedCap U (a, 1)) θ x = secondWall U θ x := by
      unfold secondWall
      rw [hU.support_insertedCap_eq_of_dominated hp hc.le hdom]
    rw [cornerWall, cornerWall, hU.firstWall_inserted_top ht hat hθ x, hsecond]
  · have hnew : support (insertedCap U (a, 1)) (companionNormal θ) =
        coordDot (a, 1) (companionNormal θ) := by
      rw [hU.support_insertedCap hp hc.le, max_eq_right (le_of_not_ge hdom)]
    have hsecond : secondWall (insertedCap U (a, 1)) θ x ≤ 0 := by
      apply (secondWall_le_iff hc).mpr
      rw [hnew]
      change a * (-Real.sin θ) + 1 * Real.cos θ - 1 ≤
        x * (-Real.sin θ) + 0 * Real.cos θ
      nlinarith [Real.cos_le_one θ, mul_nonneg (sub_nonneg.mpr hxa) hs.le]
    have hsecondOld : secondWall U θ x ≤ 0 :=
      (secondWall_mono (hU.subset_insertedCap hp) hU.nonempty hV.isCompact hc x).trans
        hsecond
    rw [max_eq_right ((min_le_right _ _).trans hsecond),
      max_eq_right ((min_le_right _ _).trans hsecondOld)]

theorem IsDownwardCap.sweptNiche_inserted_top {U : Set Plane}
    (hU : IsDownwardCap U) {a t x : ℝ} (ht : (t, 1) ∈ U) (hat : a ≤ t)
    (hxa : x ≤ a) :
    sweptNiche (insertedCap U (a, 1)) (Real.pi / 2) x =
      sweptNiche U (Real.pi / 2) x := by
  have hp : (a, (1 : ℝ)) ∈ unitStrip := by constructor <;> norm_num
  have hV := hU.isDownwardCap_insertedCap hp
  apply le_antisymm
  · apply sweptNiche_le_of_forall (by positivity)
      (sweptNiche_nonneg U (Real.pi / 2) x)
    intro θ hθ
    calc
      cornerWall (insertedCap U (a, 1)) θ x ≤
          max (cornerWall (insertedCap U (a, 1)) θ x) 0 := le_max_left _ _
      _ = max (cornerWall U θ x) 0 := hU.clippedCorner_inserted_top ht hat hθ hxa
      _ ≤ sweptNiche U (Real.pi / 2) x := max_le
        (cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCompact le_rfl x) hθ)
        (sweptNiche_nonneg U (Real.pi / 2) x)
  · exact sweptNiche_mono (hU.subset_insertedCap hp) hU.nonempty hV.isCompact
      (by positivity) le_rfl x

theorem IsDownwardCap.partialBarrier_inserted_top {U : Set Plane}
    (hU : IsDownwardCap U) {a t x : ℝ} (ht : (t, 1) ∈ U) (hat : a ≤ t)
    (hxa : x ≤ a) :
    partialBarrier (insertedCap U (a, 1)) (Real.pi / 2) x =
      partialBarrier U (Real.pi / 2) x := by
  have hp : (a, (1 : ℝ)) ∈ unitStrip := by constructor <;> norm_num
  rw [(hU.isDownwardCap_insertedCap hp).partialBarrier_pi_div_two,
    hU.partialBarrier_pi_div_two, hU.sweptNiche_inserted_top ht hat hxa]

/-- The changed support directions make no positive niche contribution on
the actual moving-window middle. The charged right wing gains strictly. -/
theorem IsDownwardCap.capScore_lt_inserted_middle_right {U : Set Plane}
    (hU : IsDownwardCap U) (hwidth : horizontalLeft U < horizontalRight U)
    {t : ℝ} (ht : (t, 1) ∈ U)
    (htRight : horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 ≤ t)
    (hlow : capRoof U
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) < 1) :
    capScore U (Real.pi / 2) <
      capScore (insertedCap U
        (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4, 1))
        (Real.pi / 2) := by
  let l := horizontalLeft U
  let r := horizontalRight U
  let a := l + (r - l) / 4
  let b := r - (r - l) / 4
  have hlr : l < r := hwidth
  have hla : l ≤ a := by dsimp [a]; linarith
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hbr : b < r := by dsimp [b]; linarith
  have hbU : b ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
    exact ⟨hla.trans hab, hbr.le⟩
  have hp : (b, (1 : ℝ)) ∈ unitStrip := by constructor <;> norm_num
  let V := insertedCap U (b, 1)
  have hV : IsDownwardCap V := hU.isDownwardCap_insertedCap hp
  have hsub : U ⊆ V := hU.subset_insertedCap hp
  have hleft : horizontalLeft V = l := hU.horizontalLeft_insertedCap hp hbU
  have hright : horizontalRight V = r := hU.horizontalRight_insertedCap hp hbU
  have hprojV : horizontalProjection V = horizontalProjection U :=
    hU.horizontalProjection_insertedCap hp hbU
  have hproj : horizontalProjection U = Icc l r :=
    horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex
  have hcU : ContinuousOn (capRoof U) (Icc l r) := by
    rw [← hproj]
    exact hU.continuousOn_capRoof
  have hcV : ContinuousOn (capRoof V) (Icc l r) := by
    rw [← hproj, ← hprojV]
    exact hV.continuousOn_capRoof
  have hleftInt : (∫ x in l..a, capRoof U x) ≤ ∫ x in l..a, capRoof V x :=
    intervalIntegral.integral_mono_on hla
      ((hcU.mono (Icc_subset_Icc le_rfl (hab.trans hbr.le))).intervalIntegrable_of_Icc hla)
      ((hcV.mono (Icc_subset_Icc le_rfl (hab.trans hbr.le))).intervalIntegrable_of_Icc hla)
      (fun x _ => hU.capRoof_mono hV hsub x)
  have hrightInt : (∫ x in b..r, capRoof U x) < ∫ x in b..r, capRoof V x := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hbr
      (hcU.mono (Icc_subset_Icc (hla.trans hab) le_rfl))
      (hcV.mono (Icc_subset_Icc (hla.trans hab) le_rfl))
      (fun x _ => hU.capRoof_mono hV hsub x)
    refine ⟨b, ⟨le_rfl, hbr.le⟩, ?_⟩
    have hroof : capRoof V b = 1 := hU.capRoof_inserted_one b
    rw [hroof]
    exact hlow
  have hmiddle : (∫ x in a..b, partialBarrier V (Real.pi / 2) x) =
      ∫ x in a..b, partialBarrier U (Real.pi / 2) x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact hU.partialBarrier_inserted_top ht htRight hx.2
  rw [hU.capScore_eq_intervalSpatialScore, hV.capScore_eq_intervalSpatialScore,
    hleft, hright]
  change (∫ x in l..a, capRoof U x) + (∫ x in b..r, capRoof U x) -
      (∫ x in a..b, partialBarrier U (Real.pi / 2) x) <
    (∫ x in l..a, capRoof V x) + (∫ x in b..r, capRoof V x) -
      (∫ x in a..b, partialBarrier V (Real.pi / 2) x)
  rw [hmiddle]
  linarith

theorem IsFullCapMaximizer.middle_right_eq_one_of_top_right {U : Set Plane}
    (hU : IsFullCapMaximizer U) {t : ℝ} (ht : (t, 1) ∈ U)
    (htRight : horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 ≤ t) :
    capRoof U (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) = 1 := by
  apply le_antisymm (capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _)
  by_contra h
  have hlow : capRoof U
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) < 1 := lt_of_not_ge h
  have hwidth : horizontalLeft U < horizontalRight U := by
    have hw := hU.width_bounds.1
    unfold capWidth at hw
    linarith [one_lt_M]
  have hstrict := hU.isCap.capScore_lt_inserted_middle_right hwidth ht htRight hlow
  have hp : (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4, (1 : ℝ))
      ∈ unitStrip := by constructor <;> norm_num
  exact (not_lt_of_ge (hU.2 _ (hU.isCap.isDownwardCap_insertedCap hp))) hstrict

end AmbidextrousSofa
