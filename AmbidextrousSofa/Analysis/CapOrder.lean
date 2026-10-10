module

public import AmbidextrousSofa.Measure.CapScore

@[expose] public section

/-!
# Order properties of actual cap walls and scores

Inclusion decreases both support walls at every first-quadrant angle,
including the genuine terminal first wall. Consequently a cap cut that
preserves the projection and the charged exterior roof cannot decrease the
scalar score. These statements concern the scalar relaxation, not the area
of a physical sofa after a geometric modification.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem firstWall_mono {U V : Set Plane} (hUV : U ⊆ V) (hne : U.Nonempty)
    (hV : IsCompact V) {θ : ℝ} (hs : 0 < Real.sin θ) (x : ℝ) :
    firstWall U θ x ≤ firstWall V θ x := by
  unfold firstWall
  exact div_le_div_of_nonneg_right
    (sub_le_sub_right (sub_le_sub_right (support_mono hUV hne hV _) 1) _) hs.le

theorem secondWall_mono {U V : Set Plane} (hUV : U ⊆ V) (hne : U.Nonempty)
    (hV : IsCompact V) {θ : ℝ} (hc : 0 < Real.cos θ) (x : ℝ) :
    secondWall U θ x ≤ secondWall V θ x := by
  unfold secondWall
  exact div_le_div_of_nonneg_right
    (add_le_add_right (sub_le_sub_right (support_mono hUV hne hV _) 1) _) hc.le

theorem cornerWall_mono {U V : Set Plane} (hUV : U ⊆ V) (hne : U.Nonempty)
    (hV : IsCompact V) {θ : ℝ} (hs : 0 < Real.sin θ) (hc : 0 < Real.cos θ)
    (x : ℝ) : cornerWall U θ x ≤ cornerWall V θ x :=
  min_le_min (firstWall_mono hUV hne hV hs x) (secondWall_mono hUV hne hV hc x)

/-- The bounded whole-angle supremum respects inclusion of actual sets. -/
theorem sweptNiche_mono {U V : Set Plane} (hUV : U ⊆ V) (hne : U.Nonempty)
    (hV : IsCompact V) {α : ℝ} (hα0 : 0 < α) (hα : α ≤ Real.pi / 2)
    (x : ℝ) : sweptNiche U α x ≤ sweptNiche V α x := by
  apply max_le _ (sweptNiche_nonneg V α x)
  apply csSup_le (sweptWallValues_nonempty U hα0 x)
  rintro y ⟨θ, hθ, rfl⟩
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1
    (by linarith [hθ.2, hα, Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.trans_le hα⟩
  exact (cornerWall_mono hUV hne hV hs hc x).trans
    (cornerWall_le_sweptNiche (sweptWallValues_bddAbove hV hα x) hθ)

/-- The true terminal wall is retained when passing the inclusion order to the barrier. -/
theorem partialBarrier_mono {U V : Set Plane} (hUV : U ⊆ V) (hne : U.Nonempty)
    (hV : IsCompact V) {α : ℝ} (hα0 : 0 < α) (hα : α ≤ Real.pi / 2)
    (x : ℝ) : partialBarrier U α x ≤ partialBarrier V α x := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0
    (by linarith [hα, Real.pi_pos])
  exact max_le_max (sweptNiche_mono hUV hne hV hα0 hα x)
    (firstWall_mono hUV hne hV hs x)

theorem IsDownwardCap.capRoof_mono {U V : Set Plane} (hU : IsDownwardCap U)
    (hV : IsDownwardCap V) (hUV : U ⊆ V) (x : ℝ) : capRoof U x ≤ capRoof V x := by
  by_cases hx : x ∈ horizontalProjection U
  · exact le_capRoof hV.isCompact (hUV (capRoof_mem hU.isCompact hx))
  · rw [capRoof_eq_zero_of_not_mem hx]
    exact capRoof_nonneg hV.isCompact (fun p hp => (hV.inStrip hp).1) x

/-- A genuine cap cut preserving every charged roof value improves the scalar score.
The common projection fixes the middle window before the integrals are compared. -/
theorem capScore_le_of_subset_of_exterior_roof_eq {U V : Set Plane}
    (hU : IsDownwardCap U) (hV : IsDownwardCap V) (hUV : U ⊆ V)
    (hprojection : horizontalProjection U = horizontalProjection V)
    (hroof : ∀ x ∈ Icc (horizontalLeft U) (horizontalRight U) \
        middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = capRoof V x)
    {α : ℝ} (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) :
    capScore V α ≤ capScore U α := by
  have hleft : horizontalLeft V = horizontalLeft U := congrArg sInf hprojection.symm
  have hright : horizontalRight V = horizontalRight U := congrArg sSup hprojection.symm
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have houter :
      (∫ x in Icc (horizontalLeft U) (horizontalRight U) \
        middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof V x) =
      ∫ x in Icc (horizontalLeft U) (horizontalRight U) \
        middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_Icc.diff
      (measurableSet_middleHalfInterval (horizontalLeft U) (horizontalRight U)))] with x hx
    exact (hroof x hx).symm
  have hbarrier :
      (∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U), partialBarrier U α x) ≤
      ∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U), partialBarrier V α x := by
    apply integral_mono
      ((integrableOn_partialBarrier_Icc hU.isCompact hα0 hα
        (horizontalLeft U) (horizontalRight U)).mono_set (middleHalfInterval_subset hlr))
      ((integrableOn_partialBarrier_Icc hV.isCompact hα0 hα
        (horizontalLeft U) (horizontalRight U)).mono_set (middleHalfInterval_subset hlr))
    exact fun x => partialBarrier_mono hUV hU.nonempty hV.isCompact hα0 hα x
  rw [capScore_eq_integrals, capScore_eq_integrals, hleft, hright, houter]
  linarith

end AmbidextrousSofa
