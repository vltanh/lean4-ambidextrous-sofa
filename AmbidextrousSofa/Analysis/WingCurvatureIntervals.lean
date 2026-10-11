module

public import AmbidextrousSofa.Analysis.AxisHeightLimit
public import AmbidextrousSofa.Analysis.MiddleMassLimit

@[expose] public section

/-!
# Actual curvature bounds on wing intervals

The exact discrete curvature sum, the selected facet estimate, and
disappearance of the uncharged middle mass give a bound on every interval
whose endpoints are non-atoms of the target curvature. Moving those
endpoints outwards through non-atoms gives the bound on every closed
interval inside a wing, including a singleton. In particular arbitrary
additional wing atoms are excluded by the actual selected sequence.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace AngularGrid

open Classical in
theorem IsSelectedPolygon.curvature_Ioc_le {target U : Set Plane}
    {boxLeft boxRight coefficient R a b : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target boxLeft boxRight level coefficient U)
    (hc : 0 ≤ coefficient) (hR : 0 ≤ R)
    (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hab : a ≤ b) (hupper : Icc a b ⊆ Ioo 0 Real.pi)
    (htop : Real.pi / 2 ∉ Icc a b) :
    (upperCurvature U).real (Ioc a b) ≤
      (4 * R + 10) * (b - a + mesh level) +
      (∑ j ∈ Finset.univ.filter (fun j : SourceIndex (dyadic level) =>
        fullAngle (dyadic level) j ∈ Icc a b), middleOuterMass U (dyadic level) j) +
      ∑ j, selectionDefect target U level coefficient j := by
  classical
  have hFG := Finset.monotone_filter_right Finset.univ
    (p := fun j : SourceIndex (dyadic level) => fullAngle (dyadic level) j ∈ Ioc a b)
    (q := fun j => fullAngle (dyadic level) j ∈ Icc a b) fun _ _ h => Ioc_subset_Icc_self h
  rw [upperCurvature_real_eq_sum_sources hU.isCap (dyadic level) hU.polygon_eq
    (Ioc_subset_Icc_self.trans hupper) (fun ht => htop (Ioc_subset_Icc_self ht))]
  refine (Finset.sum_le_sum fun j _ => hU.curvature_atom_coarse hc hR hbox j).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  gcongr ?_ + ?_ + ?_
  · exact mul_le_mul_of_nonneg_left ((Finset.sum_le_sum_of_subset_of_nonneg hFG fun _ _ _ =>
      (mesh_pos level).le).trans (sum_mesh_interval_sources_le level hab)) (by linarith)
  · exact Finset.sum_le_sum_of_subset_of_nonneg hFG fun j _ _ =>
      middleOuterMass_nonneg hU.isCap (dyadic level) j
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun j _ _ =>
      selectionDefect_nonneg target U level hc j

theorem curvature_Ioc_le_of_nonatoms
    {target : Set Plane} {U : ℕ → Set Plane}
    {boxLeft boxRight R m c a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target boxLeft boxRight (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hR : 0 ≤ R) (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hwidth : 0 < capWidth target)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hab : a ≤ b) (hupper : Icc a b ⊆ Ioo 0 Real.pi)
    (htop : Real.pi / 2 ∉ Icc a b)
    (hperp : ∀ t ∈ Icc a b, Real.cos t + m * Real.sin t ≠ 0)
    (ha : MovingSofaOptimality.sigmaAt target a = 0) (hb : MovingSofaOptimality.sigmaAt target b = 0) :
    (upperCurvature target).real (Ioc a b) ≤ (4 * R + 10) * (b - a) := by
  have hcap : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have hcb : ∀ n, MovingSofaOptimality.IsConvexBody (U n) := fun n => (hcap n).imported_isConvexBody
  have hlim := hHausdorff.imported_hausdorffTendsto hcap hTarget
  have hmass : Tendsto (fun n => (upperCurvature (U n)).real (Ioc a b)) atTop
      (𝓝 ((upperCurvature target).real (Ioc a b))) := by
    simpa only [(hcap _).upperCurvature_real_Ioc hab, hTarget.upperCurvature_real_Ioc hab] using
      (MovingSofaOptimality.ang_tendsto_sigmaFun hcb hTarget.imported_isConvexBody hlim hb).sub
        (MovingSofaOptimality.ang_tendsto_sigmaFun hcb hTarget.imported_isConvexBody hlim ha)
  have hmiddle := middleOuterMass_sum_tendsto_of_compact hHausdorff hcap hTarget
    (grid := fun n => dyadic (level n))
    (fun n => (hU n).polygon_eq) hbox hwidth haffine isCompact_Icc hupper hperp
  refine le_of_tendsto_of_tendsto hmass ?_ (Eventually.of_forall
    (fun n => (hU n).curvature_Ioc_le (hc n) hR (hbox n) hab hupper htop))
  simpa only [add_zero, Function.comp_apply] using
    ((((tendsto_const_nhds.add (mesh_tendsto.comp hlevel)).const_mul (4 * R + 10)).add
      (hmiddle.congr fun n => by rw [Finset.filter_congr_decidable])).add
      (selectionDefect_sum_tendsto (level := level) hTarget hcap hc hrate hHausdorff))

/-- Every closed subinterval of a wing obeys the linear curvature bound.
Its endpoints need not be non-atoms. The singleton case is included. -/
theorem curvature_Icc_le_on_wing
    {target : Set Plane} {U : ℕ → Set Plane}
    {boxLeft boxRight R m c A B a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target boxLeft boxRight (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hR : 0 ≤ R) (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hwidth : 0 < capWidth target)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hA : 0 ≤ A) (hB : B ≤ Real.pi) (htop : Real.pi / 2 ∉ Ioo A B)
    (hperp : ∀ t ∈ Ioo A B, Real.cos t + m * Real.sin t ≠ 0)
    (ha : A < a) (hab : a ≤ b) (hb : b < B) :
    (upperCurvature target).real (Icc a b) ≤ (4 * R + 10) * (b - a) := by
  have hC : 0 ≤ 4 * R + 10 := by linarith
  refine ge_of_tendsto (x := 𝓝[>] 0) (f := fun δ => (4 * R + 10) * (b - a + 2 * δ))
    (tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' (by fun_prop) _ _ (by simp))) ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min (sub_pos.mpr ha) (sub_pos.mpr hb))] with δ ⟨hδ0, hδ⟩
  rw [lt_min_iff] at hδ
  obtain ⟨a', ha', hfreea⟩ := exists_curvature_nonatom_Ioo target (by linarith : a - δ < a)
  obtain ⟨b', hb', hfreeb⟩ := exists_curvature_nonatom_Ioo target (by linarith : b < b + δ)
  have hsub : Icc a' b' ⊆ Ioo A B := fun t ht =>
    ⟨by linarith [ht.1, ha'.1], by linarith [ht.2, hb'.2]⟩
  refine (measureReal_mono (Icc_subset_Ioc ha'.2 hb'.1.le) measure_Ioc_lt_top.ne).trans
    ((curvature_Ioc_le_of_nonatoms hTarget hU hHausdorff hlevel hc hrate hR hbox hwidth haffine
      (by linarith [ha'.2, hb'.1]) (hsub.trans (Ioo_subset_Ioo hA hB)) (fun ht => htop (hsub ht))
      (fun t ht => hperp t (hsub ht)) hfreea hfreeb).trans
      (mul_le_mul_of_nonneg_left (by linarith [ha'.1, hb'.2]) hC))

theorem curvature_singleton_eq_zero_on_wing
    {target : Set Plane} {U : ℕ → Set Plane}
    {boxLeft boxRight R m c A B t : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target boxLeft boxRight (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hR : 0 ≤ R) (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hwidth : 0 < capWidth target)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hA : 0 ≤ A) (hB : B ≤ Real.pi) (htop : Real.pi / 2 ∉ Ioo A B)
    (hperp : ∀ s ∈ Ioo A B, Real.cos s + m * Real.sin s ≠ 0)
    (ht : t ∈ Ioo A B) : upperCurvature target {t} = 0 := by
  have h := curvature_Icc_le_on_wing hTarget hU hHausdorff hlevel hc hrate hR hbox
    hwidth haffine hA hB htop hperp ht.1 le_rfl ht.2
  rw [Icc_self, sub_self, mul_zero] at h
  exact (measureReal_eq_zero_iff isCompact_singleton.measure_ne_top).mp
    (h.antisymm measureReal_nonneg)

end AngularGrid

end AmbidextrousSofa
