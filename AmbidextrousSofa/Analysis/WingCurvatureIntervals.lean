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
  let F := Finset.univ.filter (fun j : SourceIndex (dyadic level) =>
    fullAngle (dyadic level) j ∈ Ioc a b)
  let G := Finset.univ.filter (fun j : SourceIndex (dyadic level) =>
    fullAngle (dyadic level) j ∈ Icc a b)
  have hFG : F ⊆ G := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Ioc_subset_Icc_self (Finset.mem_filter.mp hj).2⟩
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
  have hC : 0 ≤ 4 * R + 10 := by linarith
  calc
    (upperCurvature U).real (Ioc a b) =
        ∑ j ∈ F, (upperCurvature U {fullAngle (dyadic level) j}).toReal :=
      upperCurvature_real_eq_sum_sources hU.isCap (dyadic level) hU.polygon_eq
        (Ioc_subset_Icc_self.trans hupper) (fun ht => htop (Ioc_subset_Icc_self ht))
    _ ≤ ∑ j ∈ F, ((4 * R + 10) * mesh level + middleOuterMass U (dyadic level) j +
        selectionDefect target U level coefficient j) :=
      Finset.sum_le_sum (fun j _ => hU.curvature_atom_coarse hc hR hbox j)
    _ = (4 * R + 10) * (∑ j ∈ F, mesh level) +
        (∑ j ∈ F, middleOuterMass U (dyadic level) j) +
        ∑ j ∈ F, selectionDefect target U level coefficient j := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hcount hC) hmid) herr

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
    have hleft := MovingSofaOptimality.ang_tendsto_sigmaFun hcb hTarget.imported_isConvexBody hlim ha
    have hright := MovingSofaOptimality.ang_tendsto_sigmaFun hcb hTarget.imported_isConvexBody hlim hb
    have hFormula (n : ℕ) := (hcap n).upperCurvature_real_Ioc hab
    simpa only [hFormula, hTarget.upperCurvature_real_Ioc hab] using hright.sub hleft
  have hmiddle := middleOuterMass_sum_tendsto_of_compact hHausdorff hcap hTarget
    (fun n => (hU n).polygon_eq) hbox hwidth haffine isCompact_Icc hupper hperp
  have herr := selectionDefect_sum_tendsto (level := level) hTarget hcap hc hrate hHausdorff
  have hmesh := mesh_tendsto.comp hlevel
  have hrhs : Tendsto (fun n =>
      (4 * R + 10) * (b - a + mesh (level n)) +
      (∑ j ∈ Finset.univ.filter (fun j : SourceIndex (dyadic (level n)) =>
        fullAngle (dyadic (level n)) j ∈ Icc a b), middleOuterMass (U n) (dyadic (level n)) j) +
      ∑ j, selectionDefect target (U n) (level n) (coefficient n) j) atTop
        (𝓝 ((4 * R + 10) * (b - a))) := by
    have hmid' : Tendsto (fun n => ∑ j ∈ Finset.univ.filter (fun j : SourceIndex (dyadic (level n)) =>
        fullAngle (dyadic (level n)) j ∈ Icc a b), middleOuterMass (U n) (dyadic (level n)) j)
        atTop (𝓝 0) := by
      convert hmiddle using 4
    simpa only [add_zero, Function.comp_apply] using
      (((tendsto_const_nhds.add hmesh).const_mul (4 * R + 10)).add hmid').add herr
  exact le_of_tendsto_of_tendsto hmass hrhs (Eventually.of_forall
    (fun n => (hU n).curvature_Ioc_le (hc n) hR (hbox n) hab hupper htop))

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
  let C := 4 * R + 10
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have hC1 : 0 < C + 1 := by linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := min (min (a - A) (B - b)) (ε / (2 * (C + 1)))
  have hδ : 0 < δ := lt_min
    (lt_min (sub_pos.mpr ha) (sub_pos.mpr hb)) (div_pos hε (by positivity))
  have hδa : δ ≤ a - A := (min_le_left _ _).trans (min_le_left _ _)
  have hδb : δ ≤ B - b := (min_le_left _ _).trans (min_le_right _ _)
  have hδε : δ * (2 * (C + 1)) ≤ ε :=
    (le_div_iff₀ (by positivity : 0 < 2 * (C + 1))).mp (min_le_right _ _)
  obtain ⟨a', ha', hfreea⟩ := exists_curvature_nonatom_Ioo target
    (by linarith : a - δ < a)
  obtain ⟨b', hb', hfreeb⟩ := exists_curvature_nonatom_Ioo target
    (by linarith : b < b + δ)
  have ha'A : A < a' := by linarith [ha'.1]
  have hb'B : b' < B := by linarith [hb'.2]
  have hab' : a' ≤ b' := by linarith [ha'.2, hb'.1]
  have hsub : Icc a' b' ⊆ Ioo A B := fun t ht =>
    ⟨ha'A.trans_le ht.1, ht.2.trans_lt hb'B⟩
  have hbound := curvature_Ioc_le_of_nonatoms hTarget hU hHausdorff hlevel hc hrate
    hR hbox hwidth haffine hab'
    (fun t ht => ⟨hA.trans_lt (hsub ht).1, (hsub ht).2.trans_le hB⟩)
    (fun ht => htop (hsub ht)) (fun t ht => hperp t (hsub ht)) hfreea hfreeb
  have hmono : (upperCurvature target).real (Icc a b) ≤
      (upperCurvature target).real (Ioc a' b') :=
    measureReal_mono (fun x hx => ⟨ha'.2.trans_le hx.1, hx.2.trans hb'.1.le⟩)
      measure_Ioc_lt_top.ne
  have hspan : b' - a' ≤ b - a + 2 * δ := by linarith [ha'.1, hb'.2]
  have hmul := mul_le_mul_of_nonneg_left hspan hC
  change (upperCurvature target).real (Ioc a' b') ≤ C * (b' - a') at hbound
  change (upperCurvature target).real (Icc a b) ≤ C * (b - a) + ε
  nlinarith

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
  have hreal : (upperCurvature target {t}).toReal = 0 :=
    le_antisymm h ENNReal.toReal_nonneg
  exact ((ENNReal.toReal_eq_zero_iff _).mp hreal).resolve_right isCompact_singleton.measure_ne_top

end AngularGrid

end AmbidextrousSofa
