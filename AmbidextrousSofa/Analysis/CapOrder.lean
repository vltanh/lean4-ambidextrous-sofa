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
    firstWall U θ x ≤ firstWall V θ x :=
  div_le_div_of_nonneg_right
    (sub_le_sub_right (sub_le_sub_right (support_mono hUV hne hV _) 1) _) hs.le

theorem secondWall_mono {U V : Set Plane} (hUV : U ⊆ V) (hne : U.Nonempty)
    (hV : IsCompact V) {θ : ℝ} (hc : 0 < Real.cos θ) (x : ℝ) :
    secondWall U θ x ≤ secondWall V θ x :=
  div_le_div_of_nonneg_right
    (add_le_add_left (sub_le_sub_right (support_mono hUV hne hV _) 1) _) hc.le

/-- The bounded whole-angle supremum respects inclusion of actual sets. -/
theorem sweptNiche_mono {U V : Set Plane} (hUV : U ⊆ V) (hne : U.Nonempty)
    (hV : IsCompact V) {α : ℝ} (hα0 : 0 < α) (hα : α ≤ Real.pi / 2)
    (x : ℝ) : sweptNiche U α x ≤ sweptNiche V α x := by
  refine sweptNiche_le_of_forall hα0 (sweptNiche_nonneg V α x) fun θ hθ => ?_
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.trans_le hα⟩
  exact (min_le_min (firstWall_mono hUV hne hV hs x) (secondWall_mono hUV hne hV hc x)).trans
    (cornerWall_le_sweptNiche (sweptWallValues_bddAbove hV hα x) hθ)

theorem IsDownwardCap.capRoof_mono {U V : Set Plane} (hU : IsDownwardCap U)
    (hV : IsDownwardCap V) (hUV : U ⊆ V) (x : ℝ) : capRoof U x ≤ capRoof V x := by
  by_cases hx : x ∈ horizontalProjection U
  · exact le_capRoof hV.isCompact (hUV (capRoof_mem hU.isCompact hx))
  · exact (capRoof_eq_zero_of_not_mem hx).trans_le
      (capRoof_nonneg hV.isCompact (fun p hp => (hV.inStrip hp).1) x)

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
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hint {W : Set Plane} (hW : IsDownwardCap W) := (integrableOn_partialBarrier_Icc
    hW.isCompact hα0 hα _ _).mono_set (middleHalfInterval_subset hlr)
  have hs := Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [Real.pi_pos])
  rw [capScore_eq_integrals, capScore_eq_integrals,
    show horizontalLeft V = horizontalLeft U from congrArg sInf hprojection.symm,
    show horizontalRight V = horizontalRight U from congrArg sSup hprojection.symm,
    setIntegral_congr_fun (measurableSet_Icc.diff (measurableSet_middleHalfInterval _ _))
      fun x hx => (hroof x hx).symm]
  linarith [setIntegral_mono (hint hU) (hint hV) fun x => max_le_max
    (sweptNiche_mono hUV hU.nonempty hV.isCompact hα0 hα x)
    (firstWall_mono hUV hU.nonempty hV.isCompact hs x)]

end AmbidextrousSofa
