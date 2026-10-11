module

public import AmbidextrousSofa.Analysis.FiniteSourceBalance
public import AmbidextrousSofa.Analysis.RegularCurvatureDomain

@[expose] public section

/-!
# Actual selected inner-source occupation on regular wings

The normalized exposure defect is the difference between literal inner
source length and charged outer source length. Its absolute cosine
moment tends to zero by the actual endpoint laws. On compact angular
sets away from the top this controls its total variation. The omitted
middle source mass tends to zero away from the central normal. Thus the
literal finite inner-source masses converge to the actual curvature on
regular intervals. No ordinary niche-arclength identification is used.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace AngularGrid

open FinitePolygon

/-- The source mass is the sum of the actual finite graph's selected
inner lengths over the stated angular set. -/
def innerAngularMass (U : Set Plane) (grid : Finset QuarterAngle) (E : Set ℝ) : ℝ := by
  classical
  exact ∑ j ∈ Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∈ E),
    innerSourceMass U grid j

open Classical in
theorem abs_innerAngularMass_sub_curvature_le {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (hpoly : U = circumscription U (normal grid))
    {E : Set ℝ} (hupper : E ⊆ Ioo (0 : ℝ) Real.pi) (htop : Real.pi / 2 ∉ E) :
    |innerAngularMass U grid E - (upperCurvature U).real E| ≤
      (∑ j ∈ Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∈ E),
        |normalizedExposureDefect U grid j|) +
      ∑ j ∈ Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∈ E),
        middleOuterMass U grid j := by
  rw [innerAngularMass, upperCurvature_real_eq_sum_sources hU grid hpoly hupper htop,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  -- Each inner mass minus its curvature atom is the defect minus the middle outer mass.
  have htotal : (∫ x in (horizontalLeft U)..(horizontalRight U), outerDensity U grid j x) =
      (upperCurvature U {fullAngle grid j}).toReal :=
    integral_outerSource_eq_curvature_atom hU (normal grid) (normal_snd_pos grid)
      (wallSlopes_injective grid) hpoly j (normal_eq_unitNormal grid j)
  have hi := intervalIntegrable_outerDensity U grid j
  calc _ = |normalizedExposureDefect U grid j - middleOuterMass U grid j| := by
        rw [normalizedExposureDefect, finiteExposureDefect_div_eq_integrals hU, middleOuterMass,
          innerSourceMass, ← htotal, ← intervalIntegral.integral_add_adjacent_intervals (hi _
            (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4)) (hi _ _),
          ← intervalIntegral.integral_add_adjacent_intervals (hi _
            (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)) (hi _ _)]
        ring_nf
    _ ≤ _ := (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (middleOuterMass_nonneg hU grid j)])

theorem sum_cos_abs_normalizedExposureDefect_tendsto_zero_of_canonical_maximum
    {target : Set Plane} {U : ℕ → Set Plane} {a b : ℝ}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval
      (horizontalLeft target) (horizontalRight target), capRoof target x = m * x + c)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b) :
    Tendsto (fun n => ∑ j : SourceIndex (dyadic (level n)),
      |(normal (dyadic (level n)) j).1| *
        |normalizedExposureDefect (U n) (dyadic (level n)) j|) atTop (𝓝 0) := by
  have hD := erosionMoments_tendsto_zero_of_canonical_maximum hTarget hheight haffine
    hTargetBox hU hHausdorff hlevel hc hrate hleft hright
  refine squeeze_zero (fun n => Finset.sum_nonneg fun j _ => by positivity)
    (fun n => (hU n).sum_cos_abs_normalizedExposureDefect_le (hc n)) ?_
  simpa only [zero_add, mul_zero] using (hD.1.add hD.2).add ((selectionDefect_sum_tendsto
    (level := level) hTarget.isCap (fun n => (hU n).isCap) hc hrate hHausdorff).const_mul 2)

open Classical in
theorem sum_abs_defect_on_set_le_cos_sum
    (U : Set Plane) (grid : Finset QuarterAngle) {E : Set ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hE : ∀ t ∈ E, δ ≤ |Real.cos t|) :
    (∑ j ∈ Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∈ E),
      |normalizedExposureDefect U grid j|) ≤
      (∑ j : SourceIndex grid, |(normal grid j).1| * |normalizedExposureDefect U grid j|) / δ := by
  rw [le_div_iff₀ hδ, Finset.sum_mul]
  refine (Finset.sum_le_sum fun j hj => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _) fun j _ _ => by positivity)
  rw [normal_eq_unitNormal, mul_comm]
  exact mul_le_mul_of_nonneg_right (hE _ (Finset.mem_filter.mp hj).2) (abs_nonneg _)

open Classical in
/-- On any angular subset of a nonempty compact regular set, literal finite
inner-source mass and actual finite curvature have the same limit. -/
theorem innerAngularMass_sub_curvature_tendsto_of_canonical_maximum
    {target : Set Plane} {U : ℕ → Set Plane} {a b m c : ℝ}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ} {E F : Set ℝ}
    (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)
    (hF : IsCompact F) (hne : F.Nonempty) (hEF : E ⊆ F)
    (hregular : F ⊆ regularCurvatureDomain m) :
    Tendsto (fun n => innerAngularMass (U n) (dyadic (level n)) E -
      (upperCurvature (U n)).real E) atTop (𝓝 0) := by
  have hcap : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have hupper : F ⊆ Ioo (0 : ℝ) Real.pi := hregular.trans (regularCurvatureDomain_subset m)
  have htop : Real.pi / 2 ∉ F := fun h =>
    (mem_regularCurvatureDomain_iff.mp (hregular h)).2.2.1 rfl
  -- Away from the top normal, the vanishing cosine moment controls the absolute defect.
  obtain ⟨r, hr, hmin⟩ := hF.exists_isMinOn hne Real.continuous_cos.abs.continuousOn
  have hδ : 0 < |Real.cos r| := abs_pos.2 <| Real.cos_pi_div_two ▸ Real.injOn_cos.ne
    (Ioo_subset_Icc_self (hupper hr)) ⟨by positivity, by linarith [Real.pi_pos]⟩
    fun h => htop (h ▸ hr)
  have habs := squeeze_zero (fun n => Finset.sum_nonneg fun j _ => abs_nonneg _)
    (fun n => sum_abs_defect_on_set_le_cos_sum (U n) _ hδ fun x hx => hmin (hEF hx))
    (by simpa only [zero_div] using (sum_cos_abs_normalizedExposureDefect_tendsto_zero_of_canonical_maximum
      hTarget hheight ⟨m, c, haffine⟩ hTargetBox hU hHausdorff hlevel hc hrate hleft
      hright).div_const |Real.cos r|)
  -- The omitted middle source mass tends to zero away from the central normal.
  have hmid : Tendsto (fun n => ∑ j ∈ Finset.univ.filter
      (fun j : SourceIndex (dyadic (level n)) => fullAngle (dyadic (level n)) j ∈ E),
        middleOuterMass (U n) (dyadic (level n)) j) atTop (𝓝 0) :=
    squeeze_zero (fun n => Finset.sum_nonneg fun j _ => middleOuterMass_nonneg (hcap n) _ j)
      (fun n => Finset.sum_le_sum_of_subset_of_nonneg (Finset.monotone_filter_right _
        fun j _ hj => hEF hj) fun j _ _ => middleOuterMass_nonneg (hcap n) _ j)
      (middleOuterMass_sum_tendsto_of_compact hHausdorff hcap hTarget.isCap
        (fun n => (hU n).polygon_eq) (fun n => subset_symmetricBox_of_horizontalBox (hU n).inBox)
        (by linarith [hTarget.width_bounds.1, one_lt_M]) haffine hF hupper
        fun x hx => (mem_regularCurvatureDomain_iff.mp (hregular hx)).2.2.2)
  exact squeeze_zero_norm (fun n => abs_innerAngularMass_sub_curvature_le (hcap n) _
    (hU n).polygon_eq (hEF.trans hupper) fun h => htop (hEF h)) (by simpa only [zero_add] using habs.add hmid)

/-- This is source occupation, not an arclength-continuity claim: on every
compact regular interval the literal selected inner mass tends to σ. -/
theorem innerAngularMass_Ioc_tendsto_of_canonical_maximum
    {target : Set Plane} {U : ℕ → Set Plane} {a b m c s t : ℝ}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)
    (hst : s ≤ t) (hregular : Icc s t ⊆ regularCurvatureDomain m) :
    Tendsto (fun n => innerAngularMass (U n) (dyadic (level n)) (Ioc s t)) atTop
      (𝓝 ((upperCurvature target).real (Ioc s t))) := by
  have herror := innerAngularMass_sub_curvature_tendsto_of_canonical_maximum
    hTarget hheight haffine hTargetBox hU hHausdorff hlevel hc hrate hleft hright
    isCompact_Icc (nonempty_Icc.2 hst) Ioc_subset_Icc_self hregular
  -- The actual curvature masses converge since σ has no atoms at `s` and `t`.
  obtain ⟨ρ, hρ, hρbounds, _, heq⟩ := hTarget.curvature_density_on_regular_domain haffine
  have hnonatom (x : ℝ) (hx : x ∈ Icc s t) : MovingSofaOptimality.sigmaAt target x = 0 := by
    have h := measureReal_eq_integral_of_restrict_withDensity hρ (fun y => (hρbounds y).1)
      heq (measurableSet_singleton x) (singleton_subset_iff.mpr (hregular hx))
    simpa [MovingSofaOptimality.sigmaAt, upperCurvature, measureReal_def, integral_singleton] using h
  have hcap : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have hcb : ∀ n, MovingSofaOptimality.IsConvexBody (U n) := fun n => (hcap n).imported_isConvexBody
  have hlim := hHausdorff.imported_hausdorffTendsto hcap hTarget.isCap
  have hleftLim := MovingSofaOptimality.ang_tendsto_sigmaFun hcb
    hTarget.isCap.imported_isConvexBody hlim (hnonatom s ⟨le_rfl, hst⟩)
  have hrightLim := MovingSofaOptimality.ang_tendsto_sigmaFun hcb
    hTarget.isCap.imported_isConvexBody hlim (hnonatom t ⟨hst, le_rfl⟩)
  have hmass : Tendsto (fun n => (upperCurvature (U n)).real (Ioc s t)) atTop
      (𝓝 ((upperCurvature target).real (Ioc s t))) := by
    simpa only [(hcap _).upperCurvature_real_Ioc hst, hTarget.isCap.upperCurvature_real_Ioc hst]
      using hrightLim.sub hleftLim
  simpa only [sub_add_cancel, zero_add] using herror.add hmass

end AngularGrid

end AmbidextrousSofa
