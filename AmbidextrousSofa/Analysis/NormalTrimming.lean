module

public import AmbidextrousSofa.Analysis.TerminalCorner
public import AmbidextrousSofa.Analysis.EndpointTrimming

@[expose] public section

/-!
# Actual inward supporting-line cuts with unchanged projection

The cut is parametrized by its vertical displacement. Its terminal
support decreases by that displacement times the sine of the normal
angle. A strictly positive lower endpoint of the supporting face gives
a positive baseline margin, so every sufficiently small cut retains the
entire original projection and its middle interval.
-/

noncomputable section

open Set MeasureTheory MovingSofaOptimality

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
  have h : x * Real.cos α + capRoof U x * Real.sin α ≤ support U (unitNormal α) :=
    coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact hx) (unitNormal α)
  exact (le_div_iff₀ hs).mpr (by linarith)

theorem IsDownwardCap.outerSupportingRoof_contact {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hs : 0 < Real.sin α) :
    {x ∈ horizontalProjection U | outerSupportingRoof U α x - capRoof U x = 0} =
      horizontalProjection (MovingSofaOptimality.edge U α) := by
  ext x
  constructor
  · rintro ⟨hx, heq⟩
    refine ⟨(x, capRoof U x), ⟨capRoof_mem hU.isCompact hx, ?_⟩, rfl⟩
    have h := (eq_div_iff hs.ne').mp (sub_eq_zero.mp heq).symm
    change x * Real.cos α + capRoof U x * Real.sin α = support U (unitNormal α)
    linarith
  · rintro ⟨p, hp, rfl⟩
    have hline : p.1 * Real.cos α + p.2 * Real.sin α = support U (unitNormal α) := hp.2
    refine ⟨⟨p, hp.1, rfl⟩, ?_⟩
    rw [← hU.capRoof_eq_of_mem_upper_edge hs hp, sub_eq_zero, outerSupportingRoof,
      div_eq_iff hs.ne']
    linarith

/-- The lower face endpoint lies above the floor, so no baseline point
can belong to this supporting face. -/
theorem IsDownwardCap.support_right_baseline_strict {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hs : 0 < Real.sin α)
    (hface : 0 < (MovingSofaOptimality.vminus U α).2) :
    horizontalRight U * Real.cos α < support U (unitNormal α) := by
  have hp : (horizontalRight U, 0) ∈ U :=
    hU.baseline_mem_of_mem_projection (horizontalRight_mem hU.nonempty hU.isCompact)
  have hle : horizontalRight U * Real.cos α + 0 * Real.sin α ≤ support U (unitNormal α) :=
    coordDot_le_support hU.isCompact hp (unitNormal α)
  refine lt_of_le_of_ne (by linarith) fun heq => ?_
  have hmem : horizontalRight U ∈ horizontalProjection (edge U α) := ⟨_, ⟨hp,
    show horizontalRight U * Real.cos α + 0 * Real.sin α = support U (unitNormal α) by linarith⟩,
    rfl⟩
  rw [hU.horizontalProjection_edge hs.le] at hmem
  have hline : (vminus U α).1 * Real.cos α + (vminus U α).2 * Real.sin α =
      support U (unitNormal α) := dot_vminus_uvec U α
  rw [le_antisymm (hU.fst_mem_Icc (vminus_mem_edge hU.imported_isConvexBody α).1).2 hmem.2,
    ← heq] at hline
  linarith [mul_pos hface hs]

theorem IsDownwardCap.baseline_mem_normalTrim {U : Set Plane} (hU : IsDownwardCap U)
    {α ε : ℝ} (hc : 0 ≤ Real.cos α)
    (hbase : horizontalRight U * Real.cos α ≤ support U (unitNormal α) - ε * Real.sin α)
    {x : ℝ} (hx : x ∈ horizontalProjection U) : (x, 0) ∈ normalTrim U α ε :=
  ⟨hU.baseline_mem_of_mem_projection hx, show x * Real.cos α + 0 * Real.sin α ≤ _ by
    linarith [mul_le_mul_of_nonneg_right (hU.fst_mem_Icc
      (hU.baseline_mem_of_mem_projection hx)).2 hc]⟩

theorem IsDownwardCap.normalTrim {U : Set Plane} (hU : IsDownwardCap U)
    {α ε : ℝ} (hc : 0 ≤ Real.cos α) (hs : 0 ≤ Real.sin α)
    (hbase : horizontalRight U * Real.cos α ≤ support U (unitNormal α) - ε * Real.sin α) :
    IsDownwardCap (AmbidextrousSofa.normalTrim U α ε) := by
  refine ⟨⟨_, hU.baseline_mem_normalTrim hc hbase (horizontalRight_mem hU.nonempty hU.isCompact)⟩,
    hU.isCompact.inter_right
      (isClosed_le (continuous_coordDot_right (unitNormal α)) continuous_const),
    hU.convex.inter (convex_coordDot_halfspace _ _), fun p hp => hU.inStrip hp.1,
    fun p hp y hy0 hyp => ⟨hU.downward p hp.1 y hy0 hyp, ?_⟩⟩
  have hcut : p.1 * Real.cos α + p.2 * Real.sin α ≤ _ := hp.2
  show p.1 * Real.cos α + y * Real.sin α ≤ _
  linarith [mul_le_mul_of_nonneg_right hyp hs]

theorem horizontalProjection_normalTrim {U : Set Plane} (hU : IsDownwardCap U)
    {α ε : ℝ} (hc : 0 ≤ Real.cos α)
    (hbase : horizontalRight U * Real.cos α ≤ support U (unitNormal α) - ε * Real.sin α) :
    horizontalProjection (normalTrim U α ε) = horizontalProjection U :=
  Subset.antisymm (image_mono (normalTrim_subset U α ε))
    fun x hx => ⟨(x, 0), hU.baseline_mem_normalTrim hc hbase hx, rfl⟩

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

theorem support_normalTrim_eq_of_baseline {U : Set Plane} (hU : IsDownwardCap U)
    {α ε : ℝ} (hc : 0 ≤ Real.cos α) (hs : 0 < Real.sin α) (hε0 : 0 ≤ ε)
    (hbase : horizontalRight U * Real.cos α ≤ support U (unitNormal α) - ε * Real.sin α) :
    support (normalTrim U α ε) (unitNormal α) = support U (unitNormal α) - ε * Real.sin α := by
  have hv := vplus_mem_edge hU.imported_isConvexBody α
  have hline : (vplus U α).1 * Real.cos α + (vplus U α).2 * Real.sin α =
      support U (unitNormal α) := dot_vplus_uvec U α
  have hεH : ε ≤ (vplus U α).2 := (mul_le_mul_iff_left₀ hs).mp
    (by linarith [mul_le_mul_of_nonneg_right (hU.fst_mem_Icc hv.1).2 hc])
  have hpline : coordDot ((vplus U α).1, (vplus U α).2 - ε) (unitNormal α) =
      support U (unitNormal α) - ε * Real.sin α := by
    show (vplus U α).1 * Real.cos α + ((vplus U α).2 - ε) * Real.sin α = _
    linarith
  exact support_eq_of_mem (hU.normalTrim hc hs.le hbase).isCompact (fun _ hp => hp.2)
    ⟨hU.downward _ hv.1 _ (sub_nonneg.mpr hεH) (sub_le_self _ hε0), hpline.le⟩ hpline

theorem capRoof_sub_normalTrim {U : Set Plane} (hU : IsDownwardCap U)
    {α ε x : ℝ} (hc : 0 ≤ Real.cos α) (hs : 0 < Real.sin α)
    (hbase : horizontalRight U * Real.cos α ≤ support U (unitNormal α) - ε * Real.sin α)
    (hx : x ∈ horizontalProjection U) :
    capRoof U x - capRoof (normalTrim U α ε) x =
      max (ε - (outerSupportingRoof U α x - capRoof U x)) 0 := by
  have hV := hU.normalTrim hc hs.le hbase
  have hW : outerSupportingRoof U α x * Real.sin α = support U (unitNormal α) - x * Real.cos α :=
    div_mul_cancel₀ _ hs.ne'
  have hwall0 : 0 ≤ outerSupportingRoof U α x - ε := sub_nonneg.mpr ((le_div_iff₀ hs).mpr
    (by linarith [mul_le_mul_of_nonneg_right (hU.fst_mem_Icc (capRoof_mem hU.isCompact hx)).2 hc]))
  have hroof :
      capRoof (normalTrim U α ε) x = min (capRoof U x) (outerSupportingRoof U α x - ε) := by
    apply le_antisymm
    · have hp := capRoof_mem hV.isCompact
        ((horizontalProjection_normalTrim hU hc hbase).symm ▸ hx)
      have hline : x * Real.cos α + capRoof (normalTrim U α ε) x * Real.sin α ≤ _ := hp.2
      exact le_min (le_capRoof hU.isCompact hp.1)
        (le_sub_iff_add_le.mpr ((le_div_iff₀ hs).mpr (by linarith)))
    · refine le_capRoof hV.isCompact ⟨hU.downward (x, capRoof U x) (capRoof_mem hU.isCompact hx)
        _ (le_min (capRoof_nonneg hU.isCompact (fun p hp => (hU.inStrip hp).1) x) hwall0)
        (min_le_left _ _), ?_⟩
      show x * Real.cos α + min (capRoof U x) (outerSupportingRoof U α x - ε) * Real.sin α ≤ _
      linarith [mul_le_mul_of_nonneg_right (min_le_right (capRoof U x)
        (outerSupportingRoof U α x - ε)) hs.le]
  rw [hroof]
  rcases le_total (capRoof U x) (outerSupportingRoof U α x - ε) with h | h
  · rw [min_eq_left h, sub_self, max_eq_right (by linarith)]
  · rw [min_eq_right h, max_eq_left (by linarith)]
    ring

/-- The terminal facet estimate puts its entire lower endpoint strictly
above the baseline; this provides the actual admissible cut margin. -/
theorem IsJointCapMaximizer.terminal_vminus_height_ge_sin_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    Real.sin α ≤ (MovingSofaOptimality.vminus U α).2 := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hU.angle_pos
    (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hU.angle_pos, Real.pi_pos], hαL⟩
  have hw := mul_le_mul_of_nonneg_right
    (hU.terminalFaceWidth_le_reserve_of_tail_regime hregime hαL hheight haffine) hc.le
  rw [terminalTailReserve, terminalTailInset, sub_mul, div_mul_cancel₀ _ hc.ne'] at hw
  rw [hU.isCap.terminal_vminus_eq hs.ne']
  show Real.sin α ≤ (terminalTailPoint U α).2 - terminalFaceWidth U α * Real.cos α / Real.sin α
  rw [le_sub_comm, div_le_iff₀ hs]
  nlinarith [Real.sin_sq_add_cos_sq α]

end AmbidextrousSofa
