import AmbidextrousSofa.Analysis.TerminalCorner
import AmbidextrousSofa.Analysis.EndpointTrimming

/-!
# Actual inward supporting-line cuts with unchanged projection

The cut is parametrized by its vertical displacement. Its terminal
support decreases by that displacement times the sine of the normal
angle. A strictly positive lower endpoint of the supporting face gives
a positive baseline margin, so every sufficiently small cut retains the
entire original projection and its middle interval.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def outerSupportingRoof (U : Set Plane) (α x : ℝ) : ℝ :=
  (support U (unitNormal α) - x * Real.cos α) / Real.sin α

def normalTrim (U : Set Plane) (α ε : ℝ) : Set Plane :=
  U ∩ {p | coordDot p (unitNormal α) ≤ support U (unitNormal α) - ε * Real.sin α}

theorem normalTrim_subset (U : Set Plane) (α ε : ℝ) : normalTrim U α ε ⊆ U :=
  inter_subset_left

theorem continuous_outerSupportingRoof (U : Set Plane) (α : ℝ) :
    Continuous (outerSupportingRoof U α) := by
  unfold outerSupportingRoof
  fun_prop

theorem IsDownwardCap.capRoof_le_outerSupportingRoof {U : Set Plane}
    (hU : IsDownwardCap U) {α x : ℝ} (hs : 0 < Real.sin α)
    (hx : x ∈ horizontalProjection U) : capRoof U x ≤ outerSupportingRoof U α x := by
  have h := coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact hx) (unitNormal α)
  apply (le_div_iff₀ hs).mpr
  unfold coordDot unitNormal at h
  linarith only [h]

theorem IsDownwardCap.outerSupportingRoof_contact {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hs : 0 < Real.sin α) :
    {x ∈ horizontalProjection U | outerSupportingRoof U α x - capRoof U x = 0} =
      horizontalProjection (Imported.edge U α) := by
  ext x
  constructor
  · rintro ⟨hx, heq⟩
    have hline : coordDot (x, capRoof U x) (unitNormal α) = support U (unitNormal α) := by
      have hroof : capRoof U x = outerSupportingRoof U α x := by linarith only [heq]
      have h := (eq_div_iff hs.ne').mp hroof
      unfold coordDot unitNormal
      linarith only [h]
    exact ⟨(x, capRoof U x), ⟨capRoof_mem hU.isCompact hx, hline⟩, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    refine ⟨⟨p, hp.1, rfl⟩, ?_⟩
    have hroof := hU.capRoof_eq_of_mem_upper_edge hs hp
    have hline : p.1 * Real.cos α + p.2 * Real.sin α = support U (unitNormal α) := hp.2
    have heq : outerSupportingRoof U α p.1 = p.2 := by
      apply (div_eq_iff hs.ne').mpr
      linarith only [hline]
    rw [heq, ← hroof, sub_self]

/-- The lower face endpoint lies above the floor, so no baseline point
can belong to this supporting face. -/
theorem IsDownwardCap.support_right_baseline_strict {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hs : 0 < Real.sin α)
    (hface : 0 < (Imported.vminus U α).2) :
    horizontalRight U * Real.cos α < support U (unitNormal α) := by
  have hp : (horizontalRight U, 0) ∈ U := hU.baseline_mem_of_mem_projection
    (horizontalRight_mem hU.nonempty hU.isCompact)
  have hle : horizontalRight U * Real.cos α ≤ support U (unitNormal α) := by
    simpa only [coordDot, unitNormal, zero_mul, add_zero] using
      coordDot_le_support hU.isCompact hp (unitNormal α)
  apply lt_of_le_of_ne hle
  intro heq
  have hedge : (horizontalRight U, 0) ∈ Imported.edge U α := by
    refine ⟨hp, ?_⟩
    simpa only [coordDot, unitNormal, zero_mul, add_zero] using heq
  have hx : horizontalRight U ≤ (Imported.vminus U α).1 := by
    have hmem : horizontalRight U ∈ horizontalProjection (Imported.edge U α) :=
      ⟨(horizontalRight U, 0), hedge, rfl⟩
    rw [hU.horizontalProjection_edge hs.le] at hmem
    exact hmem.2
  have hx' := (hU.fst_mem_Icc (Imported.vminus_mem_edge hU.imported_isConvexBody α).1).2
  have hline : (Imported.vminus U α).1 * Real.cos α +
      (Imported.vminus U α).2 * Real.sin α = support U (unitNormal α) :=
    Imported.dot_vminus_uvec U α
  have hxeq := le_antisymm hx' hx
  rw [hxeq, ← heq] at hline
  nlinarith only [hline, mul_pos hface hs]

theorem IsDownwardCap.normalTrim {U : Set Plane} (hU : IsDownwardCap U)
    {α ε : ℝ} (hc : 0 ≤ Real.cos α) (hs : 0 ≤ Real.sin α)
    (hbase : horizontalRight U * Real.cos α ≤ support U (unitNormal α) - ε * Real.sin α) :
    IsDownwardCap (normalTrim U α ε) := by
  have hbaseline (x : ℝ) (hx : x ∈ horizontalProjection U) :
      (x, 0) ∈ normalTrim U α ε := by
    refine ⟨hU.baseline_mem_of_mem_projection hx, ?_⟩
    have hxr : x ≤ horizontalRight U :=
      le_csSup (isCompact_horizontalProjection hU.isCompact).bddAbove hx
    simpa only [coordDot, unitNormal, zero_mul, add_zero] using
      (mul_le_mul_of_nonneg_right hxr hc).trans hbase
  refine ⟨?_, ?_, ?_, fun p hp => hU.inStrip hp.1, ?_⟩
  · exact ⟨(horizontalRight U, 0), hbaseline _ (horizontalRight_mem hU.nonempty hU.isCompact)⟩
  · exact hU.isCompact.inter_right
      (isClosed_le (continuous_coordDot_right (unitNormal α)) continuous_const)
  · exact hU.convex.inter (convex_coordDot_halfspace _ _)
  · intro p hp y hy0 hyp
    refine ⟨hU.downward p hp.1 y hy0 hyp, ?_⟩
    have h := mul_le_mul_of_nonneg_right hyp hs
    have hcut := hp.2
    change p.1 * Real.cos α + y * Real.sin α ≤ _
    change p.1 * Real.cos α + p.2 * Real.sin α ≤ _ at hcut
    linarith only [h, hcut]

theorem horizontalProjection_normalTrim {U : Set Plane} (hU : IsDownwardCap U)
    {α ε : ℝ} (hc : 0 ≤ Real.cos α)
    (hbase : horizontalRight U * Real.cos α ≤ support U (unitNormal α) - ε * Real.sin α) :
    horizontalProjection (normalTrim U α ε) = horizontalProjection U := by
  apply Subset.antisymm (image_mono (normalTrim_subset U α ε))
  intro x hx
  have hxr : x ≤ horizontalRight U :=
    le_csSup (isCompact_horizontalProjection hU.isCompact).bddAbove hx
  refine ⟨(x, 0), ⟨hU.baseline_mem_of_mem_projection hx, ?_⟩, rfl⟩
  simpa only [coordDot, unitNormal, zero_mul, add_zero] using
    (mul_le_mul_of_nonneg_right hxr hc).trans hbase

theorem horizontalLeft_normalTrim {U : Set Plane} (hU : IsDownwardCap U)
    {α ε : ℝ} (hc : 0 ≤ Real.cos α)
    (hbase : horizontalRight U * Real.cos α ≤ support U (unitNormal α) - ε * Real.sin α) :
    horizontalLeft (normalTrim U α ε) = horizontalLeft U :=
  congrArg sInf (horizontalProjection_normalTrim hU hc hbase)

theorem horizontalRight_normalTrim {U : Set Plane} (hU : IsDownwardCap U)
    {α ε : ℝ} (hc : 0 ≤ Real.cos α)
    (hbase : horizontalRight U * Real.cos α ≤ support U (unitNormal α) - ε * Real.sin α) :
    horizontalRight (normalTrim U α ε) = horizontalRight U :=
  congrArg sSup (horizontalProjection_normalTrim hU hc hbase)

theorem capRoof_normalTrim {U : Set Plane} (hU : IsDownwardCap U)
    {α ε x : ℝ} (hc : 0 ≤ Real.cos α) (hs : 0 < Real.sin α)
    (hbase : horizontalRight U * Real.cos α ≤ support U (unitNormal α) - ε * Real.sin α)
    (hx : x ∈ horizontalProjection U) :
    capRoof (normalTrim U α ε) x = min (capRoof U x) (outerSupportingRoof U α x - ε) := by
  have hV := hU.normalTrim hc hs.le hbase
  have hxV : x ∈ horizontalProjection (normalTrim U α ε) := by
    rw [horizontalProjection_normalTrim hU hc hbase]
    exact hx
  have hwall0 : 0 ≤ outerSupportingRoof U α x - ε := by
    have hxr : x ≤ horizontalRight U :=
      le_csSup (isCompact_horizontalProjection hU.isCompact).bddAbove hx
    have hmul := (mul_le_mul_of_nonneg_right hxr hc).trans hbase
    apply sub_nonneg.mpr
    apply (le_div_iff₀ hs).mpr
    linarith only [hmul]
  have hroof0 : 0 ≤ capRoof U x := capRoof_nonneg hU.isCompact
    (fun p hp => (hU.inStrip hp).1) x
  apply le_antisymm
  · have hp := capRoof_mem hV.isCompact hxV
    refine le_min (le_capRoof hU.isCompact hp.1) ?_
    have hline := hp.2
    change x * Real.cos α + capRoof (normalTrim U α ε) x * Real.sin α ≤ _ at hline
    apply (le_sub_iff_add_le).mpr
    apply (le_div_iff₀ hs).mpr
    nlinarith only [hline]
  · apply le_capRoof hV.isCompact
    refine ⟨hU.downward (x, capRoof U x) (capRoof_mem hU.isCompact hx)
      _ (le_min hroof0 hwall0) (min_le_left _ _), ?_⟩
    have hmin := min_le_right (capRoof U x) (outerSupportingRoof U α x - ε)
    have hmul := mul_le_mul_of_nonneg_right hmin hs.le
    have hline : outerSupportingRoof U α x * Real.sin α =
        support U (unitNormal α) - x * Real.cos α := div_mul_cancel₀ _ hs.ne'
    change x * Real.cos α + min (capRoof U x) (outerSupportingRoof U α x - ε) *
      Real.sin α ≤ _
    nlinarith only [hmul, hline]

theorem support_normalTrim_eq {U : Set Plane} (hU : IsDownwardCap U)
    {α ε : ℝ} (hc : 0 ≤ Real.cos α) (hs : 0 ≤ Real.sin α)
    (hbase : horizontalRight U * Real.cos α ≤ support U (unitNormal α) - ε * Real.sin α)
    (hε0 : 0 ≤ ε) (hεH : ε ≤ (Imported.vplus U α).2) :
    support (normalTrim U α ε) (unitNormal α) = support U (unitNormal α) - ε * Real.sin α := by
  have hV := hU.normalTrim hc hs hbase
  let p : Plane := ((Imported.vplus U α).1, (Imported.vplus U α).2 - ε)
  have hpU : p ∈ U := hU.downward _ (Imported.vplus_mem_edge hU.imported_isConvexBody α).1
    _ (sub_nonneg.mpr hεH) (sub_le_self _ hε0)
  have hline : coordDot p (unitNormal α) = support U (unitNormal α) - ε * Real.sin α := by
    have h := Imported.dot_vplus_uvec U α
    change (Imported.vplus U α).1 * Real.cos α +
      (Imported.vplus U α).2 * Real.sin α = support U (unitNormal α) at h
    unfold p coordDot unitNormal
    nlinarith only [h]
  exact support_eq_of_mem hV.isCompact (fun _ hp => hp.2) ⟨hpU, hline.le⟩ hline

theorem support_normalTrim_eq_of_baseline {U : Set Plane} (hU : IsDownwardCap U)
    {α ε : ℝ} (hc : 0 ≤ Real.cos α) (hs : 0 < Real.sin α) (hε0 : 0 ≤ ε)
    (hbase : horizontalRight U * Real.cos α ≤ support U (unitNormal α) - ε * Real.sin α) :
    support (normalTrim U α ε) (unitNormal α) = support U (unitNormal α) - ε * Real.sin α := by
  have hx := (hU.fst_mem_Icc (Imported.vplus_mem_edge hU.imported_isConvexBody α).1).2
  have hmul := mul_le_mul_of_nonneg_right hx hc
  have hline : (Imported.vplus U α).1 * Real.cos α +
      (Imported.vplus U α).2 * Real.sin α = support U (unitNormal α) :=
    Imported.dot_vplus_uvec U α
  have hεH : ε ≤ (Imported.vplus U α).2 := by
    apply (mul_le_mul_right hs).mp
    nlinarith only [hbase, hmul, hline]
  exact support_normalTrim_eq hU hc hs.le hbase hε0 hεH

theorem capRoof_sub_normalTrim {U : Set Plane} (hU : IsDownwardCap U)
    {α ε x : ℝ} (hc : 0 ≤ Real.cos α) (hs : 0 < Real.sin α)
    (hbase : horizontalRight U * Real.cos α ≤ support U (unitNormal α) - ε * Real.sin α)
    (hx : x ∈ horizontalProjection U) :
    capRoof U x - capRoof (normalTrim U α ε) x =
      max (ε - (outerSupportingRoof U α x - capRoof U x)) 0 := by
  rw [capRoof_normalTrim hU hc hs hbase hx]
  by_cases h : capRoof U x ≤ outerSupportingRoof U α x - ε
  · rw [min_eq_left h, sub_self, max_eq_right (by linarith)]
  · rw [min_eq_right (le_of_not_ge h), max_eq_left (by linarith)]
    ring

theorem terminalTailReserve_mul_cos_div_sin (U : Set Plane) {α : ℝ}
    (hc : Real.cos α ≠ 0) (hs : Real.sin α ≠ 0) :
    terminalTailReserve U α * Real.cos α / Real.sin α =
      (terminalTailPoint U α).2 - Real.sin α := by
  unfold terminalTailReserve terminalTailInset
  field_simp [hc, hs]
  nlinarith only [Real.sin_sq_add_cos_sq α]

/-- The terminal facet estimate puts its entire lower endpoint strictly
above the baseline; this provides the actual admissible cut margin. -/
theorem IsJointCapMaximizer.terminal_vminus_height_ge_sin_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    Real.sin α ≤ (Imported.vminus U α).2 := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hU.angle_pos
    (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hU.angle_pos, Real.pi_pos], hαL⟩
  have hm := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (hU.terminalFaceWidth_le_reserve_of_tail_regime hregime hαL hheight haffine) hc.le) hs.le
  rw [terminalTailReserve_mul_cos_div_sin U hc.ne' hs.ne'] at hm
  rw [hU.isCap.terminal_vminus_eq hs.ne']
  dsimp only
  linarith only [hm]

theorem IsJointCapMaximizer.terminal_vminus_height_ge_sin
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    Real.sin α ≤ (Imported.vminus U α).2 := by
  exact IsJointCapMaximizer.terminal_vminus_height_ge_sin_of_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hαL hheight haffine) hαL hheight haffine

end AmbidextrousSofa
