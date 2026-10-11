module

public import AmbidextrousSofa.Analysis.NonpositiveCornerCurvature

@[expose] public section

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
    {t : ℝ} (ht : t ∈ S) : MovingSofaOptimality.sigmaAt U t = 0 := by
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
  have hint : LocallyIntegrable ρ volume := locallyIntegrable_iff.mpr fun K hK =>
    IntegrableOn.of_bound hK.measure_lt_top hρ.aestronglyMeasurable C (Eventually.of_forall
      fun t => (Real.norm_eq_abs _).trans_le ((abs_of_nonneg (hρ0 t)).trans_le (hρC t)))
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hint] with t hdt ht hP
  obtain ⟨a, b, htIoo, hIoo⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hS.mem_nhds ht)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨δ, hδ, hbound⟩ := hlocal t ht hP ε hε
  refine le_of_tendsto (hdt t).tendsto_slope_zero_right ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min hδ (sub_pos.mpr htIoo.2))] with d ⟨hd0, hd⟩
  rw [lt_min_iff] at hd
  rw [intervalIntegral.integral_same, sub_zero, smul_eq_mul, inv_mul_le_iff₀ hd0,
    intervalIntegral.integral_of_le (by linarith), ← measureReal_eq_integral_of_restrict_withDensity
      hρ hρ0 heq measurableSet_Ioc fun s hs => hIoo ⟨htIoo.1.trans hs.1, by linarith [hs.2]⟩]
  exact (hbound d hd0 hd.1).trans_eq (mul_comm _ _)

namespace AngularGrid

open Classical in
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
  have hFG := Finset.monotone_filter_right Finset.univ
    (p := fun j : SourceIndex (dyadic level) => fullAngle (dyadic level) j ∈ Ioc a b)
    (q := fun j => fullAngle (dyadic level) j ∈ Icc a b) fun _ _ h => Ioc_subset_Icc_self h
  rw [upperCurvature_real_eq_sum_sources hU.isCap (dyadic level) hU.polygon_eq
    (Ioc_subset_Icc_self.trans hupper) (fun ht => htop (Ioc_subset_Icc_self ht))]
  refine (Finset.sum_le_sum fun j hj => hatom j (Finset.mem_filter.mp (hFG hj)).2).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  gcongr ?_ + ?_ + ?_
  · exact mul_le_mul_of_nonneg_left ((Finset.sum_le_sum_of_subset_of_nonneg hFG fun _ _ _ =>
      (mesh_pos level).le).trans (sum_mesh_interval_sources_le level hab)) hC
  · exact Finset.sum_le_sum_of_subset_of_nonneg hFG fun j _ _ =>
      middleOuterMass_nonneg hU.isCap (dyadic level) j
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun j _ _ =>
      selectionDefect_nonneg target U level hc j

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
    (ha : MovingSofaOptimality.sigmaAt target a = 0) (hb : MovingSofaOptimality.sigmaAt target b = 0)
    (hatom : ∀ᶠ n in atTop, ∀ j : SourceIndex (dyadic (level n)),
      fullAngle (dyadic (level n)) j ∈ Icc a b →
        (upperCurvature (U n) {fullAngle (dyadic (level n)) j}).toReal ≤
          C * mesh (level n) + middleOuterMass (U n) (dyadic (level n)) j +
            selectionDefect target (U n) (level n) (coefficient n) j) :
    (upperCurvature target).real (Ioc a b) ≤ C * (b - a) := by
  have hcap : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have hcb : ∀ n, MovingSofaOptimality.IsConvexBody (U n) := fun n => (hcap n).imported_isConvexBody
  have hlim := hHausdorff.imported_hausdorffTendsto hcap hTarget
  have hupper : Icc a b ⊆ Ioo 0 Real.pi := hregular.trans (regularCurvatureDomain_subset m)
  have hmass : Tendsto (fun n => (upperCurvature (U n)).real (Ioc a b)) atTop
      (𝓝 ((upperCurvature target).real (Ioc a b))) := by
    simpa only [(hcap _).upperCurvature_real_Ioc hab, hTarget.upperCurvature_real_Ioc hab] using
      (MovingSofaOptimality.ang_tendsto_sigmaFun hcb hTarget.imported_isConvexBody hlim hb).sub
        (MovingSofaOptimality.ang_tendsto_sigmaFun hcb hTarget.imported_isConvexBody hlim ha)
  have hmiddle := middleOuterMass_sum_tendsto_of_compact hHausdorff hcap hTarget
    (grid := fun n => dyadic (level n)) (fun n => (hU n).polygon_eq) hbox hwidth haffine
    isCompact_Icc hupper fun t ht => (mem_regularCurvatureDomain_iff.mp (hregular ht)).2.2.2
  refine le_of_tendsto_of_tendsto hmass ?_ (hatom.mono fun n hn =>
    (hU n).curvature_Ioc_le_of_atom_bound (hc n) hC hab hupper
      (fun ht => (mem_regularCurvatureDomain_iff.mp (hregular ht)).2.2.1 rfl) hn)
  simpa only [add_zero, Function.comp_apply] using
    ((((tendsto_const_nhds.add (mesh_tendsto.comp hlevel)).const_mul C).add
      (hmiddle.congr fun n => by rw [Finset.filter_congr_decidable])).add
      (selectionDefect_sum_tendsto (level := level) hTarget hcap hc hrate hHausdorff))

end AngularGrid

end AmbidextrousSofa
