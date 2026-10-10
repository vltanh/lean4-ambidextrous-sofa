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

theorem IsDownwardCap.leftCompanionCap {U : Set Plane} (hU : IsDownwardCap U)
    {a : ℝ} (ha : a ∈ horizontalProjection U) : IsDownwardCap (AmbidextrousSofa.leftCompanionCap U a) := by
  have ha' := ha
  rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex] at ha'
  apply hU.horizontalCut ha'.1
  rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
  exact Icc_subset_Icc le_rfl ha'.2

theorem horizontalLeft_leftCompanionCap {U : Set Plane} (hU : IsDownwardCap U)
    {a : ℝ} (ha : a ∈ horizontalProjection U) :
    horizontalLeft (leftCompanionCap U a) = horizontalLeft U := by
  have ha' := ha
  rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex] at ha'
  apply horizontalLeft_horizontalCut hU ha'.1
  rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
  exact Icc_subset_Icc le_rfl ha'.2

theorem IsDownwardCap.rightRoof_mem_leftCompanionCap {U : Set Plane}
    (hU : IsDownwardCap U) {a : ℝ} (ha : a ∈ horizontalProjection U) :
    (a, capRoof U a) ∈ AmbidextrousSofa.leftCompanionCap U a := by
  have hpoint := capRoof_mem hU.isCompact ha
  exact ⟨hpoint, (hU.fst_mem_Icc hpoint).1, le_rfl⟩

theorem companionPointWall_nonpos_of_right {p : Plane} {x t : ℝ}
    (hpy : p.2 ≤ 1) (hxp : x ≤ p.1) (hs : 0 ≤ Real.sin t) (hc : 0 < Real.cos t) :
    companionPointWall p x t ≤ 0 := by
  have heq : companionPointWall p x t =
      (p.2 * Real.cos t + (x - p.1) * Real.sin t - 1) / Real.cos t := by
    unfold companionPointWall
    field_simp [hc.ne'] <;> ring
  rw [heq]
  apply div_nonpos_of_nonpos_of_nonneg _ hc.le
  have hheight := mul_le_mul_of_nonneg_right hpy hc.le
  have hhorizontal := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hxp) hs
  linarith only [hheight, hhorizontal, Real.cos_le_one t]

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
  have hwall : secondWall U t x = companionPointWall p x t :=
    (companionPointWall_eq_secondWall_of_support hc.ne' hsupport).symm
  rw [hwall]
  by_cases hpa : p.1 ≤ a
  · have hpV : p ∈ AmbidextrousSofa.leftCompanionCap U a := ⟨hp, (hU.fst_mem_Icc hp).1, hpa⟩
    exact (companionPointWall_le_secondWall hV hpV hc).trans (le_max_left _ _)
  · by_cases hbp : b ≤ p.1
    · exact (companionPointWall_nonpos_of_right (hU.inStrip hp).2
        (hxb.trans hbp) hs hc).trans (le_max_right _ _)
    · have hpx : p.1 ∈ Icc a b := ⟨(lt_of_not_ge hpa).le, le_of_not_ge hbp⟩
      have hpy : p.2 ≤ m * p.1 + c := by
        have h := le_capRoof hU.isCompact (show (p.1, p.2) ∈ U by simpa using hp)
        rwa [haffine p.1 hpx] at h
      have hpA : (a, m * a + c) ∈ AmbidextrousSofa.leftCompanionCap U a := by
        rw [← haffine a ⟨le_rfl, hab.le⟩]
        exact hU.rightRoof_mem_leftCompanionCap ha
      have hpB : (b, m * b + c) ∈ U := by
        rw [← haffine b ⟨hab.le, le_rfl⟩]
        exact capRoof_mem hU.isCompact hb
      have hheight := mul_le_mul_of_nonneg_right hpy hc.le
      by_cases hsign : m * Real.cos t - Real.sin t ≤ 0
      · have hhorizontal := mul_nonpos_of_nonneg_of_nonpos
          (sub_nonneg.mpr hpx.1) hsign
        have hdot : coordDot p (companionNormal t) ≤
            coordDot (a, m * a + c) (companionNormal t) := by
          unfold coordDot companionNormal
          nlinarith only [hheight, hhorizontal]
        have hpoint : companionPointWall p x t ≤ companionPointWall (a, m * a + c) x t := by
          rw [companionPointWall_eq hc.ne', companionPointWall_eq hc.ne']
          exact div_le_div_of_nonneg_right (by linarith only [hdot]) hc.le
        exact (hpoint.trans (companionPointWall_le_secondWall hV hpA hc)).trans (le_max_left _ _)
      · have hhorizontal := mul_nonpos_of_nonpos_of_nonneg
          (sub_nonpos.mpr hpx.2) (le_of_not_ge hsign)
        have hdot : coordDot p (companionNormal t) ≤
            coordDot (b, m * b + c) (companionNormal t) := by
          unfold coordDot companionNormal
          nlinarith only [hheight, hhorizontal]
        have hpoint : companionPointWall p x t ≤ companionPointWall (b, m * b + c) x t := by
          rw [companionPointWall_eq hc.ne', companionPointWall_eq hc.ne']
          exact div_le_div_of_nonneg_right (by linarith only [hdot]) hc.le
        exact (hpoint.trans (companionPointWall_nonpos_of_right (hU.inStrip hpB).2
          hxb hs hc)).trans (le_max_right _ _)

/-- Positive tilt gives exactly the low middle endpoint as the top
point of the actual left cut. No support surrogate is postulated. -/
theorem IsDownwardCap.top_leftCompanionCap_of_positive_affine
    {U : Set Plane} (hU : IsDownwardCap U) {a b m c : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (hm : 0 < m)
    (haffine : ∀ x ∈ Icc a b, capRoof U x = m * x + c) :
    capHeight (AmbidextrousSofa.leftCompanionCap U a) = capRoof U a ∧
      MovingSofaOptimality.vplus (AmbidextrousSofa.leftCompanionCap U a) (Real.pi / 2) = (a, capRoof U a) := by
  have hV := hU.leftCompanionCap ha
  have hline := haffine a ⟨le_rfl, hab.le⟩
  have hceiling (p : Plane) (hp : p ∈ AmbidextrousSofa.leftCompanionCap U a) : p.2 ≤ m * p.1 + c :=
    (le_capRoof hU.isCompact (show (p.1, p.2) ∈ U by simpa using hp.1)).trans
      (hU.capRoof_le_affine_of_affine_segment ha hb hab haffine p.1 ⟨p, hp.1, rfl⟩)
  have hheight : capHeight (AmbidextrousSofa.leftCompanionCap U a) = capRoof U a := by
    refine support_eq_of_mem hV.isCompact
      (q := (a, capRoof U a)) ?_ (hU.rightRoof_mem_leftCompanionCap ha) ?_
    · intro p hp
      have hmul := mul_le_mul_of_nonneg_left hp.2.2 hm.le
      have hy : p.2 ≤ capRoof U a := by linarith only [hceiling p hp, hmul, hline]
      simpa only [coordDot, mul_zero, mul_one, zero_add] using hy
    · simp only [coordDot, mul_zero, mul_one, zero_add]
  refine ⟨hheight, ?_⟩
  let p := MovingSofaOptimality.vplus (AmbidextrousSofa.leftCompanionCap U a) (Real.pi / 2)
  have hp : p ∈ AmbidextrousSofa.leftCompanionCap U a :=
    (MovingSofaOptimality.vplus_mem_edge hV.imported_isConvexBody _).1
  have hpy : p.2 = capRoof U a := (top_vplus_snd_eq_capHeight _).trans hheight
  have hax : a ≤ p.1 := by
    apply le_of_mul_le_mul_left _ hm
    linarith only [hceiling p hp, hpy, hline]
  exact Prod.ext (le_antisymm hp.2.2 hax) hpy

theorem IsDownwardCap.leftCompanion_initial_data_of_positive_affine
    {U : Set Plane} (hU : IsDownwardCap U) {a b m c : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (hm : 0 < m)
    (haffine : ∀ x ∈ Icc a b, capRoof U x = m * x + c) :
    companionInitialOffset (AmbidextrousSofa.leftCompanionCap U a) = a - horizontalLeft U ∧
      companionInitialDeficit (AmbidextrousSofa.leftCompanionCap U a) = 1 - capRoof U a ∧
      HasDerivWithinAt (fun t => angleSupport (AmbidextrousSofa.leftCompanionCap U a) (t + Real.pi / 2))
        (-a) (Ici 0) 0 := by
  obtain ⟨hheight, htop⟩ := hU.top_leftCompanionCap_of_positive_affine ha hb hab hm haffine
  have hderiv := (hU.leftCompanionCap ha).hasDerivWithinAt_companionSupport_zero
  rw [htop] at hderiv
  refine ⟨?_, ?_, hderiv⟩
  · unfold companionInitialOffset
    rw [htop, horizontalLeft_leftCompanionCap hU ha]
  · unfold companionInitialDeficit
    rw [hheight]

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
  have hV := hU.leftCompanionCap ha
  have hleft := horizontalLeft_leftCompanionCap hU ha
  have hbound (t : ℝ) (ht : t ∈ Icc 0 α) :
      max (secondWall (AmbidextrousSofa.leftCompanionCap U a) t x) 0 ≤
        circleHeight (companionInitialOffset (AmbidextrousSofa.leftCompanionCap U a)) -
          circleHeight (x - horizontalLeft U) +
          terminalWeightedExcess (fun r => ρ (r + Real.pi / 2))
            (Real.arcsin (companionInitialOffset (AmbidextrousSofa.leftCompanionCap U a))) := by
    have h := hV.max_secondWall_le_circle_of_density hρ hρ0 hρK heq hα0 hαL hA
      (by simpa only [hleft] using hAB) (by simpa only [hleft] using hBα)
      (by simpa only [hleft] using hsub) ht
    simpa only [hleft] using h
  apply sweptNiche_le_of_forall hα0
    ((le_max_right (secondWall (AmbidextrousSofa.leftCompanionCap U a) 0 x) 0).trans
      (hbound 0 ⟨le_rfl, hα0.le⟩))
  intro t ht
  have hs : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le
    (by linarith only [ht.2, hαL, Real.pi_pos])
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [ht.1, Real.pi_pos], ht.2.trans hαL⟩
  exact ((min_le_right _ _).trans
    (hU.secondWall_le_leftCompanionCap ha hb hab haffine hxb hs hc)).trans
      (hbound t ⟨ht.1.le, ht.2.le⟩)

end AmbidextrousSofa
