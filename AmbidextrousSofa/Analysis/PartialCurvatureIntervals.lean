module

public import AmbidextrousSofa.Analysis.PartialSourceCounting
public import AmbidextrousSofa.Analysis.MiddleMassLimit
public import AmbidextrousSofa.Analysis.AxisHeightLimit

@[expose] public section

/-!
# Actual proper-angle curvature bounds on regular intervals

The selected polygon source bound passes to every compact angular
interval separated from the top, middle-facet and terminal normals.
Non-atomic endpoints are first used for weak Stieltjes convergence and
then removed by outward approximation through non-atoms.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace PartialGrid

open AngularGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

theorem curvature_Ioc_le_of_nonatoms
    {target : Set Plane} {U : ℕ → Set Plane}
    {boxLeft boxRight R m c a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target α hαL boxLeft boxRight (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hR : 0 ≤ R) (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hwidth : 0 < capWidth target)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hab : a ≤ b) (hupper : Icc a b ⊆ Ioo 0 Real.pi)
    (htop : Real.pi / 2 ∉ Icc a b) (hterminal : (α : ℝ) ∉ Icc a b)
    (hperp : ∀ t ∈ Icc a b, Real.cos t + m * Real.sin t ≠ 0)
    (ha : MovingSofaOptimality.sigmaAt target a = 0) (hb : MovingSofaOptimality.sigmaAt target b = 0) :
    (upperCurvature target).real (Ioc a b) ≤ (8 * R + 24) * (b - a) := by
  have hcap : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have hcb : ∀ n, MovingSofaOptimality.IsConvexBody (U n) := fun n => (hcap n).imported_isConvexBody
  have hlim := hHausdorff.imported_hausdorffTendsto hcap hTarget
  have hmass : Tendsto (fun n => (upperCurvature (U n)).real (Ioc a b)) atTop
      (𝓝 ((upperCurvature target).real (Ioc a b))) := by
    have hleft := MovingSofaOptimality.ang_tendsto_sigmaFun hcb hTarget.imported_isConvexBody hlim ha
    have hright := MovingSofaOptimality.ang_tendsto_sigmaFun hcb hTarget.imported_isConvexBody hlim hb
    have hFormula (n : ℕ) := (hcap n).upperCurvature_real_Ioc hab
    simpa only [hFormula, hTarget.upperCurvature_real_Ioc hab] using hright.sub hleft
  have hmiddle := AngularGrid.middleOuterMass_sum_tendsto_of_compact hHausdorff hcap hTarget
    (grid := fun n => outerGrid α (dyadic (level n)))
    (fun n => (hU n).polygon_eq) hbox hwidth haffine isCompact_Icc hupper hperp
  have herr := selectionDefect_sum_tendsto (α := α) hTarget hcap hc hrate hHausdorff
  have hmesh := (mesh_tendsto α).comp hlevel
  have hrhs : Tendsto (fun n =>
      (8 * R + 24) * (b - a + mesh α (level n)) +
      (∑ j ∈ Finset.univ.filter (fun j : SourceIndex α (dyadic (level n)) =>
        fullAngle α (dyadic (level n)) j ∈ Icc a b), middleOuterMass (U n) α (dyadic (level n)) j) +
      ∑ j, selectionDefect target (U n) α (level n) (coefficient n) j) atTop
        (𝓝 ((8 * R + 24) * (b - a))) := by
    simpa only [add_zero] using
      (((tendsto_const_nhds.add hmesh).const_mul (8 * R + 24)).add hmiddle).add herr
  exact le_of_tendsto_of_tendsto hmass hrhs (Eventually.of_forall
    (fun n => (hU n).curvature_Ioc_le (hc n) hR (hbox n) hab hupper htop hterminal))

/-- Every closed subinterval of a wing obeys the linear curvature bound.
Its endpoints need not be non-atoms. The singleton case is included. -/
theorem curvature_Icc_le_on_wing
    {target : Set Plane} {U : ℕ → Set Plane}
    {boxLeft boxRight R m c A B a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target α hαL boxLeft boxRight (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hR : 0 ≤ R) (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hwidth : 0 < capWidth target)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hA : 0 ≤ A) (hB : B ≤ Real.pi) (htop : Real.pi / 2 ∉ Ioo A B)
    (hterminal : (α : ℝ) ∉ Ioo A B)
    (hperp : ∀ t ∈ Ioo A B, Real.cos t + m * Real.sin t ≠ 0)
    (ha : A < a) (hab : a ≤ b) (hb : b < B) :
    (upperCurvature target).real (Icc a b) ≤ (8 * R + 24) * (b - a) := by
  let C := 8 * R + 24
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
    (fun ht => htop (hsub ht)) (fun ht => hterminal (hsub ht))
    (fun t ht => hperp t (hsub ht)) hfreea hfreeb
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
    (hU : ∀ n, IsSelectedPolygon target α hαL boxLeft boxRight (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hR : 0 ≤ R) (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hwidth : 0 < capWidth target)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hA : 0 ≤ A) (hB : B ≤ Real.pi) (htop : Real.pi / 2 ∉ Ioo A B)
    (hterminal : (α : ℝ) ∉ Ioo A B)
    (hperp : ∀ s ∈ Ioo A B, Real.cos s + m * Real.sin s ≠ 0)
    (ht : t ∈ Ioo A B) : upperCurvature target {t} = 0 := by
  have h := curvature_Icc_le_on_wing hTarget hU hHausdorff hlevel hc hrate hR hbox
    hwidth haffine hA hB htop hterminal hperp ht.1 le_rfl ht.2
  rw [Icc_self, sub_self, mul_zero] at h
  have hreal : (upperCurvature target {t}).toReal = 0 :=
    le_antisymm h ENNReal.toReal_nonneg
  exact ((ENNReal.toReal_eq_zero_iff _).mp hreal).resolve_right isCompact_singleton.measure_ne_top

end PartialGrid

end AmbidextrousSofa
