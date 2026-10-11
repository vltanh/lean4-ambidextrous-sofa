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

The limit and the endpoint argument are stated for any grid and any
interval bound, so that they also serve the proper-angle polygons. The
selected sequence of a full maximizer is fixed here in a symmetric box.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace AngularGrid

open FinitePolygon

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
      ∑ j, selectionDefect target U level coefficient j :=
  upperCurvature_real_le_of_atom_bound hU.isCap (dyadic level) hU.polygon_eq
    (Ioc_subset_Icc_self.trans hupper) (fun ht => htop (Ioc_subset_Icc_self ht))
    (fun _ hj => Ioc_subset_Icc_self hj) (by linarith) (fun _ => (mesh_pos level).le)
    (middleOuterMass_nonneg hU.isCap (dyadic level)) (selectionDefect_nonneg target U level hc)
    (fun j _ => hU.curvature_atom_coarse hc hR hbox j) (sum_mesh_interval_sources_le level hab)

open Classical in
/-- An eventual bound on the curvature of `Ioc a b` for polygons on any grids, up to a vanishing
mesh `δ`, the middle-facet mass of the sources in `[a, b]` and a vanishing defect, passes to the
Hausdorff limit when `a` and `b` are not atoms of the limiting curvature. -/
theorem curvature_Ioc_le_of_eventually_le {target : Set Plane} {U : ℕ → Set Plane}
    {grid : ℕ → Finset QuarterAngle} {R m c C a b : ℝ} {δ defect : ℕ → ℝ}
    (hTarget : IsDownwardCap target) (hU : ∀ n, IsDownwardCap (U n))
    (hpoly : ∀ n, U n = circumscription (U n) (normal (grid n)))
    (hHausdorff : CapHausdorffTendsto U target) (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hwidth : 0 < capWidth target)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hab : a ≤ b) (hupper : Icc a b ⊆ Ioo 0 Real.pi)
    (hperp : ∀ t ∈ Icc a b, Real.cos t + m * Real.sin t ≠ 0)
    (ha : MovingSofaOptimality.sigmaAt target a = 0)
    (hb : MovingSofaOptimality.sigmaAt target b = 0)
    (hδ : Tendsto δ atTop (𝓝 0)) (hdefect : Tendsto defect atTop (𝓝 0))
    (hle : ∀ᶠ n in atTop, (upperCurvature (U n)).real (Ioc a b) ≤ C * (b - a + δ n) +
      (∑ j ∈ Finset.univ.filter (fun j : SourceIndex (grid n) => fullAngle (grid n) j ∈ Icc a b),
        middleOuterMass (U n) (grid n) j) + defect n) :
    (upperCurvature target).real (Ioc a b) ≤ C * (b - a) := by
  have hcb (n : ℕ) := (hU n).imported_isConvexBody
  have hlim := hHausdorff.imported_hausdorffTendsto hU hTarget
  refine le_of_tendsto_of_tendsto ?_ ?_ hle
  · simpa only [(hU _).upperCurvature_real_Ioc hab, hTarget.upperCurvature_real_Ioc hab] using
      (MovingSofaOptimality.ang_tendsto_sigmaFun hcb hTarget.imported_isConvexBody hlim hb).sub
        (MovingSofaOptimality.ang_tendsto_sigmaFun hcb hTarget.imported_isConvexBody hlim ha)
  · simpa only [add_zero] using (((hδ.const_add (b - a)).const_mul C).add
      ((middleOuterMass_sum_tendsto_of_compact hHausdorff hU hTarget hpoly hbox hwidth haffine
        isCompact_Icc hupper hperp).congr fun n => by rw [Finset.filter_congr_decidable])).add
      hdefect

/-- A bound on `Ioc a' b'` for all non-atom endpoints with `[a', b'] ⊆ (A, B)` extends to every
closed interval `[a, b] ⊆ (A, B)`: its endpoints are moved outwards through non-atoms. -/
theorem upperCurvature_real_Icc_le_of_nonatoms {target : Set Plane} {A B C a b : ℝ} (hC : 0 ≤ C)
    (h : ∀ a' b', a' ≤ b' → Icc a' b' ⊆ Ioo A B → MovingSofaOptimality.sigmaAt target a' = 0 →
      MovingSofaOptimality.sigmaAt target b' = 0 →
        (upperCurvature target).real (Ioc a' b') ≤ C * (b' - a'))
    (ha : A < a) (hab : a ≤ b) (hb : b < B) :
    (upperCurvature target).real (Icc a b) ≤ C * (b - a) := by
  refine ge_of_tendsto (x := 𝓝[>] 0) (f := fun δ => C * (b - a + 2 * δ))
    (tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' (by fun_prop) _ _ (by simp))) ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min (sub_pos.mpr ha) (sub_pos.mpr hb))] with δ ⟨hδ0, hδ⟩
  rw [lt_min_iff] at hδ
  obtain ⟨a', ha', hfreea⟩ := exists_curvature_nonatom_Ioo target (sub_lt_self a hδ0)
  obtain ⟨b', hb', hfreeb⟩ := exists_curvature_nonatom_Ioo target (lt_add_of_pos_right b hδ0)
  refine (measureReal_mono (Icc_subset_Ioc ha'.2 hb'.1.le) measure_Ioc_lt_top.ne).trans
    ((h a' b' (by linarith [ha'.2, hb'.1]) (fun t ht => ⟨by linarith [ht.1, ha'.1],
      by linarith [ht.2, hb'.2]⟩) hfreea hfreeb).trans
      (mul_le_mul_of_nonneg_left (by linarith [ha'.1, hb'.2]) hC))

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
    (upperCurvature target).real (Icc a b) ≤ (4 * R + 10) * (b - a) :=
  upperCurvature_real_Icc_le_of_nonatoms (by linarith) (fun a' b' hab' hsub ha' hb' =>
    have hupper := hsub.trans (Ioo_subset_Ioo hA hB)
    curvature_Ioc_le_of_eventually_le hTarget (fun n => (hU n).isCap) (fun n => (hU n).polygon_eq)
      hHausdorff hbox hwidth haffine hab' hupper (fun t ht => hperp t (hsub ht)) ha' hb'
      (mesh_tendsto.comp hlevel)
      (selectionDefect_sum_tendsto hTarget (fun n => (hU n).isCap) hc hrate hHausdorff)
      (.of_forall fun n => (hU n).curvature_Ioc_le (hc n) hR (hbox n) hab' hupper
        fun ht => htop (hsub ht))) ha hab hb

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

/-- A full maximizer is the Hausdorff limit of selected polygons in the symmetric box of
half-width `|horizontalLeft K| + |horizontalRight K| + 1`, with levels tending to infinity. -/
theorem IsFullCapMaximizer.exists_symmetric_selected_sequence {K : Set Plane}
    (hK : IsFullCapMaximizer K) :
    ∃ (level : ℕ → ℕ) (coefficient : ℕ → ℝ) (U : ℕ → Set Plane), Tendsto level atTop atTop ∧
      (∀ n, 0 ≤ coefficient n) ∧ Tendsto coefficient atTop (𝓝 0) ∧
      (∀ n, AngularGrid.IsSelectedPolygon K (-(|horizontalLeft K| + |horizontalRight K| + 1))
        (|horizontalLeft K| + |horizontalRight K| + 1) (level n) (coefficient n) (U n)) ∧
      CapHausdorffTendsto U K := by
  obtain ⟨level, coefficient, U, hlevel, hc, hrate, hU, -, hHausdorff⟩ :=
    AngularGrid.exists_selected_sequence hK (neg_le_self (by positivity))
      (subset_symmetricBox_of_horizontalBox fun p hp =>
        ⟨hK.isCap.fst_mem_Icc hp, hK.isCap.inStrip hp⟩)
  exact ⟨level, coefficient, U, tendsto_atTop_mono hlevel tendsto_id, fun n => (hc n).le, hrate,
    hU, hHausdorff⟩

end AmbidextrousSofa
