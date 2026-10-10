module

public import AmbidextrousSofa.Analysis.PartialRegularDomain
public import AmbidextrousSofa.Analysis.PartialHorizontalCutoff
public import AmbidextrousSofa.Analysis.SourceOccupation

@[expose] public section

/-!
# Actual source occupation for proper selected polygons

The inner source sum includes the whole terminal first wall. Its exact
difference from curvature is the normalized exposure defect minus the
middle source mass. The actual endpoint laws make the cosine moment of
the absolute defect vanish, and compact regular angular sets avoid the
top and middle normals. On regular intervals the resulting inner source
mass therefore tends to the literal curvature of the proper maximizer.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa
namespace PartialGrid

open FinitePolygon AngularGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

def innerAngularMass (U : Set Plane) (α : TerminalAngle)
    (hαL : (α : ℝ) < Real.pi / 2) (grid : Finset QuarterAngle) (E : Set ℝ) : ℝ := by
  classical
  exact ∑ j ∈ Finset.univ.filter (fun j : SourceIndex α grid => fullAngle α grid j ∈ E),
    innerSourceMass U α hαL grid j

theorem innerAngularMass_nonneg {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (E : Set ℝ) : 0 ≤ innerAngularMass U α hαL grid E := by
  classical
  exact Finset.sum_nonneg (fun j _ => innerSourceMass_nonneg hU α hαL grid j)

theorem innerSourceMass_sub_atom_eq {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (hpoly : U = circumscription U (normal α grid))
    (j : SourceIndex α grid) :
    innerSourceMass U α hαL grid j - (upperCurvature U {fullAngle α grid j}).toReal =
      normalizedExposureDefect U α hαL grid j - middleOuterMass U α grid j := by
  have hdef := finiteExposureDefect_div_eq_integrals (α := α) (hαL := hαL) hU grid j
  have htotal := integral_outerSource_eq_curvature_atom hU (normal α grid)
    (normal_snd_pos α grid) (wallSlopes_injective α grid) hpoly j (normal_eq_unitNormal α grid j)
  have hleft := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_outerDensity U α grid j (horizontalLeft U)
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4))
    (intervalIntegrable_outerDensity U α grid j
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4))
  have hright := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_outerDensity U α grid j (horizontalLeft U)
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4))
    (intervalIntegrable_outerDensity U α grid j
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) (horizontalRight U))
  change (∫ x in (horizontalLeft U)..(horizontalRight U), outerDensity U α grid j x) =
    (upperCurvature U {fullAngle α grid j}).toReal at htotal
  dsimp only [innerSourceMass, normalizedExposureDefect, middleOuterMass,
    AngularGrid.middleOuterMass, capWidth]
  linarith only [hdef, htotal, hleft, hright]

open Classical in
theorem abs_innerAngularMass_sub_curvature_le {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (hpoly : U = circumscription U (normal α grid))
    {E : Set ℝ} (hupper : E ⊆ Ioo (0 : ℝ) Real.pi) (htop : Real.pi / 2 ∉ E) :
    |innerAngularMass U α hαL grid E - (upperCurvature U).real E| ≤
      (∑ j ∈ Finset.univ.filter (fun j : SourceIndex α grid => fullAngle α grid j ∈ E),
        |normalizedExposureDefect U α hαL grid j|) +
      ∑ j ∈ Finset.univ.filter (fun j : SourceIndex α grid => fullAngle α grid j ∈ E),
        middleOuterMass U α grid j := by
  classical
  have heq : innerAngularMass U α hαL grid E - (upperCurvature U).real E =
      ∑ j ∈ Finset.univ.filter (fun j : SourceIndex α grid => fullAngle α grid j ∈ E),
        (normalizedExposureDefect U α hαL grid j - middleOuterMass U α grid j) := by
    rw [innerAngularMass,
      AngularGrid.upperCurvature_real_eq_sum_sources hU (outerGrid α grid) hpoly hupper htop,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => innerSourceMass_sub_atom_eq hU grid hpoly j)
  rw [heq, ← Finset.sum_add_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  calc
    |normalizedExposureDefect U α hαL grid j - middleOuterMass U α grid j| ≤
        |normalizedExposureDefect U α hαL grid j| + |-(middleOuterMass U α grid j)| := by
      simpa only [sub_eq_add_neg] using
        abs_add_le (normalizedExposureDefect U α hαL grid j) (-(middleOuterMass U α grid j))
    _ = _ := by rw [abs_neg, abs_of_nonneg (middleOuterMass_nonneg hU α grid j)]

open Classical in
theorem sum_abs_defect_on_set_tendsto_of_compact
    {U : ℕ → Set Plane} {grid : ℕ → Finset QuarterAngle} {E F : Set ℝ}
    (hcos : Tendsto (fun n => ∑ j : SourceIndex α (grid n),
      |(normal α (grid n) j).1| * |normalizedExposureDefect (U n) α hαL (grid n) j|)
        atTop (𝓝 0))
    (hF : IsCompact F) (hEF : E ⊆ F) (hupper : F ⊆ Ioo (0 : ℝ) Real.pi)
    (htop : Real.pi / 2 ∉ F) :
    Tendsto (fun n => ∑ j ∈ Finset.univ.filter
      (fun j : SourceIndex α (grid n) => fullAngle α (grid n) j ∈ E),
        |normalizedExposureDefect (U n) α hαL (grid n) j|) atTop (𝓝 0) := by
  classical
  by_cases hne : F.Nonempty
  · obtain ⟨t, ht, hmin⟩ := hF.exists_isMinOn hne Real.continuous_cos.abs.continuousOn
    have hδ : 0 < |Real.cos t| := abs_pos.mpr
      (cos_ne_zero_of_upper_ne_top (hupper ht) (fun heq => htop (heq ▸ ht)))
    apply squeeze_zero (fun n => Finset.sum_nonneg (fun j _ => abs_nonneg _))
      (fun n => sum_abs_defect_on_set_le_cos_sum (α := α) (hαL := hαL) (U n) (grid n) hδ
        (fun s hs => hmin (hEF hs)))
    simpa only [zero_div] using hcos.div_const |Real.cos t|
  · have hFempty := Set.not_nonempty_iff_eq_empty.mp hne
    have hEempty : E = ∅ := subset_empty_iff.mp (hFempty ▸ hEF)
    simp only [hEempty, Set.mem_empty_iff_false, Finset.filter_false, Finset.sum_empty]
    exact tendsto_const_nhds

theorem innerAngularMass_sub_curvature_tendsto_of_canonical_maximum
    {target : Set Plane} {U : ℕ → Set Plane} {a b m c : ℝ}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ} {E F : Set ℝ}
    (hTarget : IsJointCapMaximizer target α) (hheight : capHeight target = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target α hαL a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)
    (hF : IsCompact F) (hEF : E ⊆ F)
    (hregular : F ⊆ regularProperCurvatureDomain α m) :
    Tendsto (fun n => innerAngularMass (U n) α hαL (dyadic (level n)) E -
      (upperCurvature (U n)).real E) atTop (𝓝 0) := by
  classical
  have hupper : F ⊆ Ioo (0 : ℝ) Real.pi :=
    hregular.trans (regularProperCurvatureDomain_subset α m)
  have htop : Real.pi / 2 ∉ F := by
    intro h
    exact (mem_regularCurvatureDomain_iff.mp (hregular h).1).2.2.1 rfl
  have hperp : ∀ t ∈ F, Real.cos t + m * Real.sin t ≠ 0 :=
    fun t ht => (mem_regularCurvatureDomain_iff.mp (hregular ht).1).2.2.2
  have hcos := sum_cos_abs_normalizedExposureDefect_tendsto_zero_of_canonical_maximum
    hTarget hheight ⟨m, c, haffine⟩ hTargetBox hU hHausdorff hlevel hc hrate hleft hright
  have habs := sum_abs_defect_on_set_tendsto_of_compact hcos hF hEF hupper htop
  have hbox : ∀ n, U n ⊆ Icc (-(|a| + |b| + 1)) (|a| + |b| + 1) ×ˢ Icc (0 : ℝ) 1 :=
    fun n => subset_symmetricBox_of_horizontalBox (hU n).inBox
  have hwidth : 0 < capWidth target := by linarith only [hTarget.width_bounds.1, one_lt_M]
  have hmidF := AngularGrid.middleOuterMass_sum_tendsto_of_compact hHausdorff
    (fun n => (hU n).isCap) hTarget.isCap
    (grid := fun n => outerGrid α (dyadic (level n))) (fun n => (hU n).polygon_eq)
    hbox hwidth haffine hF hupper hperp
  have hmidE : Tendsto (fun n => ∑ j ∈ Finset.univ.filter
      (fun j : SourceIndex α (dyadic (level n)) => fullAngle α (dyadic (level n)) j ∈ E),
        middleOuterMass (U n) α (dyadic (level n)) j) atTop (𝓝 0) := by
    apply squeeze_zero
      (fun n => Finset.sum_nonneg (fun j _ => middleOuterMass_nonneg (hU n).isCap α _ j))
      (fun n => ?_) hmidF
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hEF (Finset.mem_filter.mp hj).2⟩
    · intro j _ _
      exact middleOuterMass_nonneg (hU n).isCap α _ j
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq, sub_zero]
  exact squeeze_zero (fun n => abs_nonneg _)
    (fun n => abs_innerAngularMass_sub_curvature_le (hU n).isCap _ (hU n).polygon_eq
      (hEF.trans hupper) (fun ht => htop (hEF ht)))
    (by simpa only [zero_add] using habs.add hmidE)

/-- All interval endpoints are actual non-atoms, proved from the proper
source density. The caller supplies no occupation or non-atomicity law. -/
theorem innerAngularMass_Ioc_tendsto_of_canonical_maximum
    {target : Set Plane} {U : ℕ → Set Plane} {a b m c s t : ℝ}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsJointCapMaximizer target α) (hheight : capHeight target = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target α hαL a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)
    (hst : s ≤ t) (hregular : Icc s t ⊆ regularProperCurvatureDomain α m) :
    Tendsto (fun n => innerAngularMass (U n) α hαL (dyadic (level n)) (Ioc s t)) atTop
      (𝓝 ((upperCurvature target).real (Ioc s t))) := by
  have herror := innerAngularMass_sub_curvature_tendsto_of_canonical_maximum
    hTarget hheight haffine hTargetBox hU hHausdorff hlevel hc hrate hleft hright
    isCompact_Icc Ioc_subset_Icc_self hregular
  have hnonatom (x : ℝ) (hx : x ∈ Icc s t) : MovingSofaOptimality.sigmaAt target x = 0 :=
    hTarget.sigmaAt_eq_zero_on_regular_proper_domain hαL haffine (hregular hx)
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

end PartialGrid
end AmbidextrousSofa
