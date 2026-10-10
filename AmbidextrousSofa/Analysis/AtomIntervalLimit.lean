import AmbidextrousSofa.Analysis.NonpositiveCornerCurvature

/-!
# From actual selected atoms to local density inequalities

These lemmas retain the actual middle-face and support-selection errors
when summing a finite atom bound. Their proved vanishing limits then give
an interval bound for the actual target curvature. A conditional local
bound is transferred to any bounded density of that measure by the
global Lebesgue differentiation theorem.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem sigmaAt_eq_zero_of_density {U : Set Plane} {S : Set ℝ} {ρ : ℝ → ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t)
    (heq : (upperCurvature U).restrict S =
      (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    {t : ℝ} (ht : t ∈ S) : Imported.sigmaAt U t = 0 := by
  change (upperCurvature U).real {t} = 0
  rw [measureReal_eq_integral_of_restrict_withDensity hρ hρ0 heq (measurableSet_singleton t)
    (singleton_subset_iff.mpr ht)]
  simp

theorem ae_density_le_of_conditional_local_bound
    {μ : Measure ℝ} {ρ f : ℝ → ℝ} {S : Set ℝ} {P : ℝ → Prop} {C : ℝ}
    (hS : IsOpen S) (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (heq : μ.restrict S = (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hlocal : ∀ t ∈ S, P t → ∀ ε > 0,
      ∃ δ > 0, ∀ d : ℝ, 0 < d → d < δ → μ.real (Ioc t (t + d)) ≤ (f t + ε) * d) :
    ∀ᵐ t : ℝ ∂volume, t ∈ S → P t → ρ t ≤ f t := by
  have hint : LocallyIntegrable ρ volume := by
    apply locallyIntegrable_iff.mpr
    intro K hK
    apply IntegrableOn.of_bound hK.measure_lt_top hρ.aestronglyMeasurable C
    exact Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hρ0 t)]
      exact hρC t)
  filter_upwards [hint.ae_hasDerivAt_integral] with t hdt ht hP
  have hderiv := hdt t
  have hstep : Tendsto AngularGrid.selectionRate atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨AngularGrid.selectionRate_tendsto, Eventually.of_forall AngularGrid.selectionRate_pos⟩
  have hquot : Tendsto (fun n =>
      (∫ s in t..(t + AngularGrid.selectionRate n), ρ s) / AngularGrid.selectionRate n)
      atTop (𝓝 (ρ t)) := by
    simpa only [intervalIntegral.integral_same, sub_zero, smul_eq_mul,
      div_eq_mul_inv, mul_comm] using hderiv.tendsto_slope_zero_right.comp hstep
  obtain ⟨a, b, htIoo, hIoo⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hS.mem_nhds ht)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hlocal t ht hP ε hε
  apply le_of_tendsto hquot
  filter_upwards [AngularGrid.selectionRate_tendsto.eventually (isOpen_Iio.mem_nhds hδ),
    AngularGrid.selectionRate_tendsto.eventually
      (isOpen_Iio.mem_nhds (sub_pos.mpr htIoo.2))] with n hnδ hnb
  have hpos := AngularGrid.selectionRate_pos n
  have hsub : Ioc t (t + AngularGrid.selectionRate n) ⊆ S := by
    intro s hs
    apply hIoo
    exact ⟨htIoo.1.trans hs.1, by linarith [hs.2]⟩
  have hmass : μ.real (Ioc t (t + AngularGrid.selectionRate n)) =
      ∫ s in t..(t + AngularGrid.selectionRate n), ρ s := by
    rw [intervalIntegral.integral_of_le (by linarith : t ≤ t + AngularGrid.selectionRate n)]
    exact measureReal_eq_integral_of_restrict_withDensity hρ hρ0 heq measurableSet_Ioc hsub
  have h := hbound (AngularGrid.selectionRate n) hpos hnδ
  rw [hmass] at h
  exact (div_le_iff₀ hpos).mpr h

namespace AngularGrid

theorem IsSelectedPolygon.curvature_Ioc_le_of_atom_bound
    {target U : Set Plane} {boxLeft boxRight coefficient C a b : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target boxLeft boxRight level coefficient U)
    (hc : 0 ≤ coefficient) (hC : 0 ≤ C) (hab : a ≤ b)
    (hupper : Icc a b ⊆ Ioo 0 Real.pi) (htop : Real.pi / 2 ∉ Icc a b)
    (hatom : ∀ j : SourceIndex (dyadic level), fullAngle (dyadic level) j ∈ Icc a b →
      (upperCurvature U {fullAngle (dyadic level) j}).toReal ≤ C * mesh level +
        middleOuterMass U (dyadic level) j + selectionDefect target U level coefficient j) :
    (upperCurvature U).real (Ioc a b) ≤
      C * (b - a + mesh level) +
      (∑ j ∈ Finset.univ.filter (fun j : SourceIndex (dyadic level) =>
        fullAngle (dyadic level) j ∈ Icc a b), middleOuterMass U (dyadic level) j) +
      ∑ j, selectionDefect target U level coefficient j := by
  classical
  let F := Finset.univ.filter (fun j : SourceIndex (dyadic level) =>
    fullAngle (dyadic level) j ∈ Ioc a b)
  let G := Finset.univ.filter (fun j : SourceIndex (dyadic level) =>
    fullAngle (dyadic level) j ∈ Icc a b)
  have hFG : F ⊆ G := by
    intro j hj
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Ioc_subset_Icc_self (Finset.mem_filter.mp hj).2⟩
  have hcount : (∑ j ∈ F, mesh level) ≤ b - a + mesh level := by
    apply le_trans ?_ (sum_mesh_interval_sources_le level hab)
    exact Finset.sum_le_sum_of_subset_of_nonneg hFG (fun _ _ _ => (mesh_pos level).le)
  have hmid : (∑ j ∈ F, middleOuterMass U (dyadic level) j) ≤
      ∑ j ∈ G, middleOuterMass U (dyadic level) j :=
    Finset.sum_le_sum_of_subset_of_nonneg hFG
      (fun j _ _ => middleOuterMass_nonneg hU.isCap (dyadic level) j)
  have herr : (∑ j ∈ F, selectionDefect target U level coefficient j) ≤
      ∑ j, selectionDefect target U level coefficient j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun j _ _ => selectionDefect_nonneg target U level hc j)
  calc
    (upperCurvature U).real (Ioc a b) =
        ∑ j ∈ F, (upperCurvature U {fullAngle (dyadic level) j}).toReal :=
      upperCurvature_real_eq_sum_sources hU.isCap (dyadic level) hU.polygon_eq
        (Ioc_subset_Icc_self.trans hupper) (fun ht => htop (Ioc_subset_Icc_self ht))
    _ ≤ ∑ j ∈ F, (C * mesh level + middleOuterMass U (dyadic level) j +
        selectionDefect target U level coefficient j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hatom j (Finset.mem_filter.mp (hFG hj)).2
    _ = C * (∑ j ∈ F, mesh level) +
        (∑ j ∈ F, middleOuterMass U (dyadic level) j) +
          ∑ j ∈ F, selectionDefect target U level coefficient j := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hcount hC) hmid) herr

theorem curvature_Ioc_le_of_eventual_atom_bound
    {target : Set Plane} {U : ℕ → Set Plane}
    {boxLeft boxRight R m c C a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target boxLeft boxRight (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hwidth : 0 < capWidth target)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hC : 0 ≤ C) (hab : a ≤ b) (hregular : Icc a b ⊆ regularCurvatureDomain m)
    (ha : Imported.sigmaAt target a = 0) (hb : Imported.sigmaAt target b = 0)
    (hatom : ∀ᶠ n in atTop, ∀ j : SourceIndex (dyadic (level n)),
      fullAngle (dyadic (level n)) j ∈ Icc a b →
        (upperCurvature (U n) {fullAngle (dyadic (level n)) j}).toReal ≤
          C * mesh (level n) + middleOuterMass (U n) (dyadic (level n)) j +
            selectionDefect target (U n) (level n) (coefficient n) j) :
    (upperCurvature target).real (Ioc a b) ≤ C * (b - a) := by
  have hcap : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have hcb : ∀ n, Imported.IsConvexBody (U n) := fun n => (hcap n).imported_isConvexBody
  have hlim := hHausdorff.imported_hausdorffTendsto hcap hTarget
  have hupper : Icc a b ⊆ Ioo 0 Real.pi := hregular.trans (regularCurvatureDomain_subset m)
  have htop : Real.pi / 2 ∉ Icc a b := by
    intro ht
    exact (mem_regularCurvatureDomain_iff.mp (hregular ht)).2.2.1 rfl
  have hperp : ∀ t ∈ Icc a b, Real.cos t + m * Real.sin t ≠ 0 :=
    fun t ht => (mem_regularCurvatureDomain_iff.mp (hregular ht)).2.2.2
  have hmass : Tendsto (fun n => (upperCurvature (U n)).real (Ioc a b)) atTop
      (𝓝 ((upperCurvature target).real (Ioc a b))) := by
    have hleft := Imported.ang_tendsto_sigmaFun hcb hTarget.imported_isConvexBody hlim ha
    have hright := Imported.ang_tendsto_sigmaFun hcb hTarget.imported_isConvexBody hlim hb
    have hFormula (n : ℕ) := (hcap n).upperCurvature_real_Ioc hab
    simpa only [hFormula, hTarget.upperCurvature_real_Ioc hab] using hright.sub hleft
  have hmiddle := middleOuterMass_sum_tendsto_of_compact hHausdorff hcap hTarget
    (fun n => (hU n).polygon_eq) hbox hwidth haffine isCompact_Icc hupper hperp
  have herr := selectionDefect_sum_tendsto hTarget hcap hc hrate hHausdorff
  have hmesh := mesh_tendsto.comp hlevel
  have hrhs : Tendsto (fun n => C * (b - a + mesh (level n)) +
      (∑ j ∈ Finset.univ.filter (fun j : SourceIndex (dyadic (level n)) =>
        fullAngle (dyadic (level n)) j ∈ Icc a b), middleOuterMass (U n) (dyadic (level n)) j) +
      ∑ j, selectionDefect target (U n) (level n) (coefficient n) j) atTop
        (𝓝 (C * (b - a))) := by
    simpa only [add_zero] using
      (((tendsto_const_nhds.add hmesh).const_mul C).add hmiddle).add herr
  apply le_of_tendsto_of_tendsto hmass hrhs
  filter_upwards [hatom] with n hn
  exact (hU n).curvature_Ioc_le_of_atom_bound (hc n) hC hab hupper htop hn

end AngularGrid

end AmbidextrousSofa
