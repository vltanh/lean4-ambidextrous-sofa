module

public import AmbidextrousSofa.Analysis.LocalSourceDensity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

@[expose] public section

/-!
# Sharp densities for the actual wing curvature

The coarse bound already supplies an actual bounded density. The local
sharp source estimate is applied to small positive intervals, and the
Lebesgue differentiation theorem identifies their limiting average with
that density. Thus the neighboring-wall coefficient bounds the actual
Radon–Nikodym density. A final null-set modification makes both its
nonnegativity and the sharp bound hold everywhere.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem measureReal_eq_integral_of_restrict_withDensity
    {μ : Measure ℝ} {ρ : ℝ → ℝ} {S s : Set ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (heq : μ.restrict S = (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hs : MeasurableSet s) (hsub : s ⊆ S) :
    μ.real s = ∫ t in s, ρ t := by
  have h : μ s = μ.restrict S s := by rw [Measure.restrict_apply hs, inter_eq_left.mpr hsub]
  rw [measureReal_def, h, heq, withDensity_apply _ hs, Measure.restrict_restrict_of_subset hsub,
    integral_eq_lintegral_of_nonneg_ae (.of_forall hρ0) hρ.aestronglyMeasurable]

open AngularGrid in
/-- A local interval estimate controls the actual density at its Lebesgue
points. The coefficient need not be continuous. -/
theorem density_le_of_local_interval_bound
    {μ : Measure ℝ} {ρ f : ℝ → ℝ} {a b C : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : μ.restrict (Ioo a b) =
      (volume.restrict (Ioo a b)).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hlocal : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ ε > 0,
      ∃ δ > 0, ∀ d : ℝ, 0 < d → d < δ →
        μ.real (Ioc t (t + d)) ≤ (f t + ε) * d) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), ρ t ≤ f t := by
  have hint : IntervalIntegrable ρ volume a b :=
    (IntegrableOn.of_bound isCompact_uIcc.measure_lt_top hρ.aestronglyMeasurable C
      (.of_forall fun t => (abs_of_nonneg (hρ0 t)).trans_le (hρC t))).intervalIntegrable
  filter_upwards [hlocal, ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae hint.ae_hasDerivAt_integral] with t htlocal ht hdt
  have htcc := Icc_subset_uIcc (Ioo_subset_Icc_self ht)
  have hquot : Tendsto (fun n => (∫ s in t..(t + selectionRate n), ρ s) / selectionRate n)
      atTop (𝓝 (ρ t)) := by
    simpa only [intervalIntegral.integral_same, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm,
      Function.comp_def] using (hdt htcc t htcc).tendsto_slope_zero_right.comp
        (tendsto_nhdsWithin_iff.mpr ⟨selectionRate_tendsto, .of_forall selectionRate_pos⟩)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨δ, hδ, hbound⟩ := htlocal ε hε
  refine le_of_tendsto hquot ?_
  filter_upwards [selectionRate_tendsto.eventually (isOpen_Iio.mem_nhds hδ),
    selectionRate_tendsto.eventually (isOpen_Iio.mem_nhds (sub_pos.mpr ht.2))] with n hnδ hnb
  have hpos := selectionRate_pos n
  rw [div_le_iff₀ hpos, intervalIntegral.integral_of_le (by linarith),
    ← measureReal_eq_integral_of_restrict_withDensity hρ hρ0 heq measurableSet_Ioc
      fun s hs => ⟨ht.1.trans hs.1, by linarith [hs.2]⟩]
  exact hbound _ hpos hnδ

namespace AngularGrid

/-- RG3 for an actual selected sequence. Both source families are covered
by their full upper normal; their exceptional companion atoms are a null
set and do not need a regularity hypothesis. -/
theorem curvature_density_sharp_on_wing
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
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ sourceKappa (upperCornerVelocity target t)) ∧
      (∀ t, ρ t ≤ 4 * R + 10) ∧
      (upperCurvature target).restrict (Ioo a b) =
        (volume.restrict (Ioo a b)).withDensity (fun t => ENNReal.ofReal (ρ t)) := by
  obtain ⟨ρ, hρ, hρbounds, heq⟩ := curvature_density_on_wing hTarget hU hHausdorff hlevel
    hc hrate hR hbox hwidth haffine hA hB htop hperp ha hab hb
  have hsharp : ∀ᵐ t ∂volume.restrict (Ioo a b),
      ρ t ≤ sourceKappa (upperCornerVelocity target t) := by
    refine density_le_of_local_interval_bound hρ (fun t => (hρbounds t).1)
      (fun t => (hρbounds t).2) heq ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae (ae_sigmaAt_companionSourceAngle_eq_zero target)] with t ht hcomp ε hε
    obtain ⟨δ, hδ, -, hlocal⟩ := curvature_local_source_bound hTarget hU hHausdorff hlevel
      hc hrate hR hbox hwidth haffine hA hB htop hperp ⟨ha.trans ht.1, ht.2.trans hb⟩ hcomp hε
    refine ⟨δ, hδ, fun d hd hdδ => ?_⟩
    simpa only [add_sub_cancel_left] using
      hlocal t (t + d) (by linarith) (by linarith) (by linarith)
  refine ⟨fun t => min (ρ t) (sourceKappa (upperCornerVelocity target t)),
    hρ.min (continuous_sourceKappa.measurable.comp hTarget.measurable_upperCornerVelocity),
    fun t => ⟨le_min (hρbounds t).1 (sourceKappa_nonneg _), min_le_right _ _⟩,
    fun t => (min_le_left _ _).trans (hρbounds t).2, heq.trans (withDensity_congr_ae ?_)⟩
  filter_upwards [hsharp] with t ht
  rw [min_eq_left ht]

theorem curvature_restrict_le_source_density
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
    (upperCurvature target).restrict (Ioo a b) ≤
      (volume.restrict (Ioo a b)).withDensity
        (fun t => ENNReal.ofReal (sourceKappa (upperCornerVelocity target t))) := by
  obtain ⟨ρ, _, hρ, _, heq⟩ := curvature_density_sharp_on_wing hTarget hU hHausdorff hlevel
    hc hrate hR hbox hwidth haffine hA hB htop hperp ha hab hb
  exact heq ▸ withDensity_mono (.of_forall fun t => ENNReal.ofReal_le_ofReal (hρ t).2)

end AngularGrid

end AmbidextrousSofa
