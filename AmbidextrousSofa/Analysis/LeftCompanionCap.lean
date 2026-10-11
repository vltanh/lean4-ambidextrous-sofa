module

public import AmbidextrousSofa.Analysis.TerminalCompanionComparison
public import AmbidextrousSofa.Analysis.EndpointTrimming
public import AmbidextrousSofa.Analysis.FacetPinning

@[expose] public section

/-!
# The actual left charged companion cap

Cut the original cap vertically at the left endpoint of its affine
middle. Points on the high wing contribute nonpositive companion walls
on the middle window. The affine middle is controlled by its two
endpoints, and its left endpoint belongs to the cut cap. Thus the cut
cap controls every positive historical companion wall of the original
cap, in every sign of the middle slope.

For positive middle slope, the cut cap has the unique top point given
by the actual low middle endpoint. This proves its initial support
height and right derivative directly. Its curvature-density transfer
is a separate obligation; no regularity is inferred merely from cutting.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

def leftCompanionCap (U : Set Plane) (a : ℝ) : Set Plane :=
  horizontalCut U (horizontalLeft U) a

theorem leftCompanionCap_subset (U : Set Plane) (a : ℝ) : leftCompanionCap U a ⊆ U :=
  horizontalCut_subset U (horizontalLeft U) a

private theorem left_cut {U : Set Plane} (hU : IsDownwardCap U) {a : ℝ}
    (ha : a ∈ horizontalProjection U) :
    horizontalLeft U ≤ a ∧ Icc (horizontalLeft U) a ⊆ horizontalProjection U := by
  rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex] at ha ⊢
  exact ⟨ha.1, Icc_subset_Icc le_rfl ha.2⟩

theorem IsDownwardCap.leftCompanionCap {U : Set Plane} (hU : IsDownwardCap U)
    {a : ℝ} (ha : a ∈ horizontalProjection U) :
    IsDownwardCap (AmbidextrousSofa.leftCompanionCap U a) :=
  (left_cut hU ha).elim hU.horizontalCut

theorem horizontalLeft_leftCompanionCap {U : Set Plane} (hU : IsDownwardCap U)
    {a : ℝ} (ha : a ∈ horizontalProjection U) :
    horizontalLeft (leftCompanionCap U a) = horizontalLeft U :=
  (left_cut hU ha).elim (horizontalLeft_horizontalCut hU)

theorem IsDownwardCap.rightRoof_mem_leftCompanionCap {U : Set Plane}
    (hU : IsDownwardCap U) {a : ℝ} (ha : a ∈ horizontalProjection U) :
    (a, capRoof U a) ∈ AmbidextrousSofa.leftCompanionCap U a :=
  ⟨capRoof_mem hU.isCompact ha, (left_cut hU ha).1, le_rfl⟩

theorem companionPointWall_nonpos_of_right {p : Plane} {x t : ℝ}
    (hpy : p.2 ≤ 1) (hxp : x ≤ p.1) (hs : 0 ≤ Real.sin t) (hc : 0 < Real.cos t) :
    companionPointWall p x t ≤ 0 := by
  rw [companionPointWall_eq hc.ne']
  refine div_nonpos_of_nonpos_of_nonneg ?_ hc.le
  simp only [coordDot, companionNormal]
  linarith [mul_nonneg (sub_nonneg.2 hxp) hs, mul_nonneg (sub_nonneg.2 hpy) hc.le,
    Real.cos_le_one t]

/-- The high wing is nonpositive and the affine middle is controlled
by its endpoints. The resulting bound is for the actual support of the
original cap, not merely for a selected finite family of points. -/
theorem IsDownwardCap.secondWall_le_leftCompanionCap
    {U : Set Plane} (hU : IsDownwardCap U) {a b m c x t : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (haffine : ∀ y ∈ Icc a b, capRoof U y = m * y + c)
    (hxb : x ≤ b) (hs : 0 ≤ Real.sin t) (hc : 0 < Real.cos t) :
    secondWall U t x ≤ max (secondWall (AmbidextrousSofa.leftCompanionCap U a) t x) 0 := by
  have hV := hU.leftCompanionCap ha
  obtain ⟨p, hp, hsupport⟩ := exists_coordDot_eq_support hU.isCompact hU.nonempty
    (companionNormal t)
  rw [← companionPointWall_eq_secondWall_of_support hc.ne' hsupport]
  rcases le_or_gt p.1 a with hpa | hpa
  · exact (companionPointWall_le_secondWall hV ⟨hp, (hU.fst_mem_Icc hp).1, hpa⟩ hc).trans
      (le_max_left _ _)
  rcases le_or_gt b p.1 with hbp | hbp
  · exact (companionPointWall_nonpos_of_right (hU.inStrip hp).2 (hxb.trans hbp) hs hc).trans
      (le_max_right _ _)
  have hpy := (le_capRoof hU.isCompact hp).trans_eq (haffine p.1 ⟨hpa.le, hbp.le⟩)
  have hpoint (q : ℝ) (hq : 0 ≤ (q - p.1) * (m * Real.cos t - Real.sin t)) :
      companionPointWall p x t ≤ companionPointWall (q, m * q + c) x t := by
    rw [companionPointWall_eq hc.ne', companionPointWall_eq hc.ne']
    refine div_le_div_of_nonneg_right ?_ hc.le
    simp only [coordDot, companionNormal]
    linarith [mul_le_mul_of_nonneg_right hpy hc.le]
  rcases le_total (m * Real.cos t - Real.sin t) 0 with hsign | hsign
  · exact ((hpoint a (mul_nonneg_of_nonpos_of_nonpos (by linarith) hsign)).trans
      (companionPointWall_le_secondWall hV (haffine a ⟨le_rfl, hab.le⟩ ▸
        hU.rightRoof_mem_leftCompanionCap ha) hc)).trans (le_max_left _ _)
  · exact ((hpoint b (mul_nonneg (by linarith) hsign)).trans (companionPointWall_nonpos_of_right
      (haffine b ⟨hab.le, le_rfl⟩ ▸ (hU.inStrip (capRoof_mem hU.isCompact hb)).2) hxb hs hc)).trans
      (le_max_right _ _)

/-- Positive tilt gives exactly the low middle endpoint as the top
point of the actual left cut. No support surrogate is postulated. -/
theorem IsDownwardCap.top_leftCompanionCap_of_positive_affine
    {U : Set Plane} (hU : IsDownwardCap U) {a b m c : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (hm : 0 < m)
    (haffine : ∀ x ∈ Icc a b, capRoof U x = m * x + c) :
    capHeight (AmbidextrousSofa.leftCompanionCap U a) = capRoof U a ∧
      MovingSofaOptimality.vplus (AmbidextrousSofa.leftCompanionCap U a) (Real.pi / 2) =
        (a, capRoof U a) := by
  have hV := hU.leftCompanionCap ha
  have hline := haffine a ⟨le_rfl, hab.le⟩
  have hceiling (p : Plane) (hp : p ∈ AmbidextrousSofa.leftCompanionCap U a) :
      p.2 ≤ m * p.1 + c :=
    (le_capRoof hU.isCompact hp.1).trans
      (hU.capRoof_le_affine_of_affine_segment ha hb hab haffine p.1 ⟨p, hp.1, rfl⟩)
  have hheight : capHeight (AmbidextrousSofa.leftCompanionCap U a) = capRoof U a :=
    support_eq_of_mem hV.isCompact (fun p hp => by
      simp only [coordDot, mul_zero, mul_one, zero_add]
      linarith [hceiling p hp, mul_le_mul_of_nonneg_left hp.2.2 hm.le])
      (hU.rightRoof_mem_leftCompanionCap ha) (by simp [coordDot])
  have hp := (MovingSofaOptimality.vplus_mem_edge hV.imported_isConvexBody (Real.pi / 2)).1
  have hpy := (top_vplus_snd_eq_capHeight _).trans hheight
  exact ⟨hheight, Prod.ext (le_antisymm hp.2.2
    (le_of_mul_le_mul_left (by linarith [hceiling _ hp]) hm)) hpy⟩

/-- The actual left-wing density controls the visited niche of the
original cap. This includes the positive-tilt case with its true low
endpoint height deficit and right derivative. -/
theorem IsDownwardCap.sweptNiche_le_circle_of_leftCompanion_density
    {U : Set Plane} (hU : IsDownwardCap U) {S : Set ℝ} {ρ : ℝ → ℝ}
    {a b m c K α x : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (haffine : ∀ y ∈ Icc a b, capRoof U y = m * y + c)
    (hxb : x ≤ b)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature (AmbidextrousSofa.leftCompanionCap U a)).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (hA : 0 < companionInitialOffset (AmbidextrousSofa.leftCompanionCap U a))
    (hAB : companionInitialOffset (AmbidextrousSofa.leftCompanionCap U a) ≤ x - horizontalLeft U)
    (hBα : x - horizontalLeft U < Real.sin α)
    (hsub : Ioc (Real.pi / 2)
      (Real.arcsin (x - horizontalLeft U) + Real.pi / 2) ⊆ S) :
    sweptNiche U α x ≤
      circleHeight (companionInitialOffset (AmbidextrousSofa.leftCompanionCap U a)) -
        circleHeight (x - horizontalLeft U) +
        terminalWeightedExcess (fun t => ρ (t + Real.pi / 2))
          (Real.arcsin (companionInitialOffset (AmbidextrousSofa.leftCompanionCap U a))) := by
  rw [← horizontalLeft_leftCompanionCap hU ha] at hAB hBα hsub ⊢
  have hbound (r : ℝ) (hr : r ∈ Icc 0 α) :=
    (hU.leftCompanionCap ha).max_secondWall_le_circle_of_density hρ hρ0 hρK heq hα0 hαL hA hAB
      hBα hsub hr
  refine sweptNiche_le_of_forall hα0 ((le_max_right _ 0).trans (hbound 0 ⟨le_rfl, hα0.le⟩))
    fun t ht => ((min_le_right _ _).trans (hU.secondWall_le_leftCompanionCap ha hb hab haffine hxb
      (Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le (by linarith [ht.2, Real.pi_pos]))
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2.trans hαL⟩))).trans
      (hbound t ⟨ht.1.le, ht.2.le⟩)

end AmbidextrousSofa
