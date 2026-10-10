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

theorem cos_ne_zero_of_upper_ne_top {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) Real.pi) (htop : t ≠ Real.pi / 2) : Real.cos t ≠ 0 := by
  intro hz
  have heq := (cos_add_mul_sin_eq_zero_iff (m := 0) ht).mp
    (by simpa only [zero_mul, add_zero] using hz)
  apply htop
  simpa only [affineNormalAngle, Real.arctan_zero, zero_add] using heq

namespace AngularGrid

open FinitePolygon

/-- The source mass is the sum of the actual finite graph's selected
inner lengths over the stated angular set. -/
def innerAngularMass (U : Set Plane) (grid : Finset QuarterAngle) (E : Set ℝ) : ℝ := by
  classical
  exact ∑ j ∈ Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∈ E),
    innerSourceMass U grid j

theorem innerAngularMass_nonneg {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (E : Set ℝ) : 0 ≤ innerAngularMass U grid E := by
  classical
  exact Finset.sum_nonneg (fun j _ => innerSourceMass_nonneg hU grid j)

theorem innerSourceMass_sub_atom_eq {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (hpoly : U = circumscription U (normal grid))
    (j : SourceIndex grid) :
    innerSourceMass U grid j - (upperCurvature U {fullAngle grid j}).toReal =
      normalizedExposureDefect U grid j - middleOuterMass U grid j := by
  classical
  have hdef := finiteExposureDefect_div_eq_integrals hU grid j
  have htotal := integral_outerSource_eq_curvature_atom hU (normal grid)
    (normal_snd_pos grid) (wallSlopes_injective grid) hpoly j (normal_eq_unitNormal grid j)
  have hleft := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_outerDensity U grid j (horizontalLeft U)
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4))
    (intervalIntegrable_outerDensity U grid j
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4))
  have hright := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_outerDensity U grid j (horizontalLeft U)
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4))
    (intervalIntegrable_outerDensity U grid j
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) (horizontalRight U))
  change (∫ x in (horizontalLeft U)..(horizontalRight U), outerDensity U grid j x) =
    (upperCurvature U {fullAngle grid j}).toReal at htotal
  dsimp only [innerSourceMass, normalizedExposureDefect, middleOuterMass]
  linarith

open Classical in
theorem abs_innerAngularMass_sub_curvature_le {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (hpoly : U = circumscription U (normal grid))
    {E : Set ℝ} (hupper : E ⊆ Ioo (0 : ℝ) Real.pi) (htop : Real.pi / 2 ∉ E) :
    |innerAngularMass U grid E - (upperCurvature U).real E| ≤
      (∑ j ∈ Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∈ E),
        |normalizedExposureDefect U grid j|) +
      ∑ j ∈ Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∈ E),
        middleOuterMass U grid j := by
  classical
  have heq : innerAngularMass U grid E - (upperCurvature U).real E =
      ∑ j ∈ Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∈ E),
        (normalizedExposureDefect U grid j - middleOuterMass U grid j) := by
    rw [innerAngularMass, upperCurvature_real_eq_sum_sources hU grid hpoly hupper htop,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => innerSourceMass_sub_atom_eq hU grid hpoly j)
  rw [heq, ← Finset.sum_add_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  calc
    |normalizedExposureDefect U grid j - middleOuterMass U grid j| ≤
        |normalizedExposureDefect U grid j| + |-(middleOuterMass U grid j)| := by
      simpa only [sub_eq_add_neg] using
        abs_add_le (normalizedExposureDefect U grid j) (-(middleOuterMass U grid j))
    _ = _ := by rw [abs_neg, abs_of_nonneg (middleOuterMass_nonneg hU grid j)]

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
  have herr := selectionDefect_sum_tendsto (level := level) hTarget.isCap (fun n => (hU n).isCap)
    hc hrate hHausdorff
  apply squeeze_zero
    (fun n => Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
    (fun n => (hU n).sum_cos_abs_normalizedExposureDefect_le (hc n))
  simpa only [zero_add, mul_zero] using (hD.1.add hD.2).add (herr.const_mul 2)

open Classical in
theorem sum_abs_defect_on_set_le_cos_sum
    (U : Set Plane) (grid : Finset QuarterAngle) {E : Set ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hE : ∀ t ∈ E, δ ≤ |Real.cos t|) :
    (∑ j ∈ Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∈ E),
      |normalizedExposureDefect U grid j|) ≤
      (∑ j : SourceIndex grid, |(normal grid j).1| * |normalizedExposureDefect U grid j|) / δ := by
  classical
  apply (le_div_iff₀ hδ).mpr
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∈ E),
        |(normal grid j).1| * |normalizedExposureDefect U grid j| := by
      apply Finset.sum_le_sum
      intro j hj
      have h := hE (fullAngle grid j) (Finset.mem_filter.mp hj).2
      have hn : (normal grid j).1 = Real.cos (fullAngle grid j) := by
        rw [normal_eq_unitNormal]
        rfl
      rw [hn, mul_comm]
      exact mul_le_mul_of_nonneg_right h (abs_nonneg _)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun j _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))

open Classical in
/-- Away from the top normal, the actual vanishing cosine moment controls
the full absolute exposure defect, including every tie-selected source. -/
theorem sum_abs_defect_on_set_tendsto_of_compact
    {U : ℕ → Set Plane} {grid : ℕ → Finset QuarterAngle} {E F : Set ℝ}
    (hcos : Tendsto (fun n => ∑ j : SourceIndex (grid n),
      |(normal (grid n) j).1| * |normalizedExposureDefect (U n) (grid n) j|) atTop (𝓝 0))
    (hF : IsCompact F) (hEF : E ⊆ F) (hupper : F ⊆ Ioo (0 : ℝ) Real.pi)
    (htop : Real.pi / 2 ∉ F) :
    Tendsto (fun n => ∑ j ∈ Finset.univ.filter
      (fun j : SourceIndex (grid n) => fullAngle (grid n) j ∈ E),
        |normalizedExposureDefect (U n) (grid n) j|) atTop (𝓝 0) := by
  classical
  by_cases hne : F.Nonempty
  · obtain ⟨t, ht, hmin⟩ := hF.exists_isMinOn hne Real.continuous_cos.abs.continuousOn
    have hδ : 0 < |Real.cos t| := abs_pos.mpr
      (cos_ne_zero_of_upper_ne_top (hupper ht) (fun heq => htop (heq ▸ ht)))
    apply squeeze_zero (fun n => Finset.sum_nonneg (fun j _ => abs_nonneg _))
      (fun n => sum_abs_defect_on_set_le_cos_sum (U n) (grid n) hδ
        (fun s hs => hmin (hEF hs)))
    simpa only [zero_div] using hcos.div_const |Real.cos t|
  · have hFempty := Set.not_nonempty_iff_eq_empty.mp hne
    have hEempty : E = ∅ := subset_empty_iff.mp (hFempty ▸ hEF)
    simp only [hEempty, Set.mem_empty_iff_false, Finset.filter_false, Finset.sum_empty]
    exact tendsto_const_nhds

/-- On any angular subset of a compact regular set, literal finite
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
    (hF : IsCompact F) (hEF : E ⊆ F) (hregular : F ⊆ regularCurvatureDomain m) :
    Tendsto (fun n => innerAngularMass (U n) (dyadic (level n)) E -
      (upperCurvature (U n)).real E) atTop (𝓝 0) := by
  classical
  have hupper : F ⊆ Ioo (0 : ℝ) Real.pi :=
    hregular.trans (regularCurvatureDomain_subset m)
  have htop : Real.pi / 2 ∉ F := by
    intro h
    exact (mem_regularCurvatureDomain_iff.mp (hregular h)).2.2.1 rfl
  have hperp : ∀ t ∈ F, Real.cos t + m * Real.sin t ≠ 0 :=
    fun t ht => (mem_regularCurvatureDomain_iff.mp (hregular ht)).2.2.2
  have hcos := sum_cos_abs_normalizedExposureDefect_tendsto_zero_of_canonical_maximum
    hTarget hheight ⟨m, c, haffine⟩ hTargetBox hU hHausdorff hlevel hc hrate hleft hright
  have habs := sum_abs_defect_on_set_tendsto_of_compact hcos hF hEF hupper htop
  have hbox : ∀ n, U n ⊆ Icc (-(|a| + |b| + 1)) (|a| + |b| + 1) ×ˢ Icc (0 : ℝ) 1 :=
    fun n => subset_symmetricBox_of_horizontalBox (hU n).inBox
  have hwidth : 0 < capWidth target := by linarith [hTarget.width_bounds.1, one_lt_M]
  have hmidF := middleOuterMass_sum_tendsto_of_compact hHausdorff
    (fun n => (hU n).isCap) hTarget.isCap (fun n => (hU n).polygon_eq)
    hbox hwidth haffine hF hupper hperp
  have hmidE : Tendsto (fun n => ∑ j ∈ Finset.univ.filter
      (fun j : SourceIndex (dyadic (level n)) => fullAngle (dyadic (level n)) j ∈ E),
        middleOuterMass (U n) (dyadic (level n)) j) atTop (𝓝 0) := by
    apply squeeze_zero
      (fun n => Finset.sum_nonneg (fun j _ => middleOuterMass_nonneg (hU n).isCap _ j))
      (fun n => ?_) hmidF
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hEF (Finset.mem_filter.mp hj).2⟩
    · intro j _ _
      exact middleOuterMass_nonneg (hU n).isCap _ j
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq, sub_zero]
  exact squeeze_zero (fun n => abs_nonneg _)
    (fun n => abs_innerAngularMass_sub_curvature_le (hU n).isCap _ (hU n).polygon_eq
      (hEF.trans hupper) (fun ht => htop (hEF ht)))
    (by simpa only [zero_add] using habs.add hmidE)

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
    isCompact_Icc Ioc_subset_Icc_self hregular
  obtain ⟨ρ, hρ, hρbounds, _, heq⟩ := hTarget.curvature_density_on_regular_domain haffine
  have hnonatom (x : ℝ) (hx : x ∈ Icc s t) : MovingSofaOptimality.sigmaAt target x = 0 := by
    have h := measureReal_eq_integral_of_restrict_withDensity hρ (fun y => (hρbounds y).1)
      heq (measurableSet_singleton x) (singleton_subset_iff.mpr (hregular hx))
    simpa [MovingSofaOptimality.sigmaAt, upperCurvature, measureReal_def, integral_singleton] using h
  have hcap : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have hcb : ∀ n, MovingSofaOptimality.IsConvexBody (U n) := fun n => (hcap n).imported_isConvexBody
  have hlim := hHausdorff.imported_hausdorffTendsto hcap hTarget.isCap
  have hleftLim := MovingSofaOptimality.ang_tendsto_sigmaFun hcb hTarget.isCap.imported_isConvexBody hlim
    (hnonatom s ⟨le_rfl, hst⟩)
  have hrightLim := MovingSofaOptimality.ang_tendsto_sigmaFun hcb hTarget.isCap.imported_isConvexBody hlim
    (hnonatom t ⟨hst, le_rfl⟩)
  have hmass : Tendsto (fun n => (upperCurvature (U n)).real (Ioc s t)) atTop
      (𝓝 ((upperCurvature target).real (Ioc s t))) := by
    have hFormula (n : ℕ) := (hcap n).upperCurvature_real_Ioc hst
    simpa only [hFormula, hTarget.isCap.upperCurvature_real_Ioc hst] using hrightLim.sub hleftLim
  simpa only [sub_add_cancel, zero_add] using herror.add hmass

end AngularGrid

end AmbidextrousSofa
