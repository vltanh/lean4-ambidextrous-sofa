import AmbidextrousSofa.Analysis.LocalSourceDensity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

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
  have hmeasure : μ s = ∫⁻ t in s, ENNReal.ofReal (ρ t) := by
    calc
      μ s = μ.restrict S s := by rw [Measure.restrict_apply hs, inter_eq_left.mpr hsub]
      _ = (volume.restrict S).withDensity (fun t => ENNReal.ofReal (ρ t)) s := by rw [heq]
      _ = ∫⁻ t in s, ENNReal.ofReal (ρ t) := by
        rw [withDensity_apply _ hs, Measure.restrict_restrict_of_subset hsub]
  rw [measureReal_def, hmeasure]
  exact (integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hρ0)
    hρ.aestronglyMeasurable).symm

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
  have hint : IntervalIntegrable ρ volume a b := by
    apply IntegrableOn.intervalIntegrable
    apply IntegrableOn.of_bound isCompact_uIcc.measure_lt_top hρ.aestronglyMeasurable C
    exact Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hρ0 t)]
      exact hρC t)
  have hdiff := hint.ae_hasDerivAt_integral
  filter_upwards [hlocal, ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae hdiff] with t htlocal ht hdt
  have hab : a ≤ b := le_of_lt (ht.1.trans ht.2)
  have htcc : t ∈ uIcc a b := by
    rw [uIcc_of_le hab]
    exact ⟨ht.1.le, ht.2.le⟩
  have hderiv := hdt htcc t htcc
  have hstep : Tendsto AngularGrid.selectionRate atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨AngularGrid.selectionRate_tendsto, Eventually.of_forall AngularGrid.selectionRate_pos⟩
  have hquot : Tendsto (fun n =>
      (∫ s in t..(t + AngularGrid.selectionRate n), ρ s) / AngularGrid.selectionRate n)
      atTop (𝓝 (ρ t)) := by
    simpa only [intervalIntegral.integral_same, sub_zero, smul_eq_mul,
      div_eq_mul_inv, mul_comm] using hderiv.tendsto_slope_zero_right.comp hstep
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := htlocal ε hε
  apply le_of_tendsto hquot
  filter_upwards [AngularGrid.selectionRate_tendsto.eventually (isOpen_Iio.mem_nhds hδ),
    AngularGrid.selectionRate_tendsto.eventually
      (isOpen_Iio.mem_nhds (sub_pos.mpr ht.2))] with n hnδ hnb
  have hpos := AngularGrid.selectionRate_pos n
  have hsub : Ioc t (t + AngularGrid.selectionRate n) ⊆ Ioo a b := by
    intro s hs
    exact ⟨ht.1.trans hs.1, by linarith [hs.2]⟩
  have hmass : μ.real (Ioc t (t + AngularGrid.selectionRate n)) =
      ∫ s in t..(t + AngularGrid.selectionRate n), ρ s := by
    rw [intervalIntegral.integral_of_le (by linarith : t ≤ t + AngularGrid.selectionRate n)]
    exact measureReal_eq_integral_of_restrict_withDensity hρ hρ0 heq measurableSet_Ioc hsub
  have h := hbound (AngularGrid.selectionRate n) hpos hnδ
  rw [hmass] at h
  exact (div_le_iff₀ hpos).mpr h

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
    apply density_le_of_local_interval_bound hρ (fun t => (hρbounds t).1)
      (fun t => (hρbounds t).2) heq
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae (ae_sigmaAt_companionSourceAngle_eq_zero target)] with t ht hcomp
    intro ε hε
    have htwing : t ∈ Ioo A B := ⟨ha.trans ht.1, ht.2.trans hb⟩
    obtain ⟨δ, hδ, _, hlocal⟩ := curvature_local_source_bound hTarget hU hHausdorff hlevel
      hc hrate hR hbox hwidth haffine hA hB htop hperp htwing hcomp hε
    refine ⟨δ, hδ, ?_⟩
    intro d hd hdδ
    have h := hlocal t (t + d) (by linarith) (by linarith) (by linarith)
    simpa only [add_sub_cancel_left] using h
  let η := fun t => min (ρ t) (sourceKappa (upperCornerVelocity target t))
  have hη : Measurable η :=
    hρ.min (continuous_sourceKappa.measurable.comp hTarget.measurable_upperCornerVelocity)
  refine ⟨η, hη, ?_, ?_, heq.trans ?_⟩
  · intro t
    exact ⟨le_min (hρbounds t).1 (sourceKappa_nonneg _), min_le_right _ _⟩
  · intro t
    exact (min_le_left _ _).trans (hρbounds t).2
  · apply withDensity_congr_ae
    filter_upwards [hsharp] with t ht
    change ENNReal.ofReal (ρ t) = ENNReal.ofReal (min (ρ t) _)
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
  rw [heq]
  exact withDensity_mono (Eventually.of_forall (fun t => ENNReal.ofReal_le_ofReal (hρ t).2))

end AngularGrid

/-- The full maximizer theorem constructs its own convergent selected
sequence. Its sharp curvature density is an output of the actual cap
geometry, not a supplied variational certificate. -/
theorem IsFullCapMaximizer.curvature_density_sharp_on_wing {K : Set Plane}
    (hK : IsFullCapMaximizer K) {m c A B a b : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c)
    (hA : 0 ≤ A) (hB : B ≤ Real.pi) (htop : Real.pi / 2 ∉ Ioo A B)
    (hperp : ∀ t ∈ Ioo A B, Real.cos t + m * Real.sin t ≠ 0)
    (ha : A < a) (hab : a ≤ b) (hb : b < B) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ sourceKappa (upperCornerVelocity K t)) ∧
      (∀ t, ρ t ≤ 4 * (|horizontalLeft K| + |horizontalRight K| + 1) + 10) ∧
      (upperCurvature K).restrict (Ioo a b) =
        (volume.restrict (Ioo a b)).withDensity (fun t => ENNReal.ofReal (ρ t)) := by
  let R := |horizontalLeft K| + |horizontalRight K| + 1
  have hR : 0 ≤ R := by positivity
  have hbox : K ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1 := by
    apply subset_symmetricBox_of_horizontalBox
    intro p hp
    refine ⟨?_, hK.isCap.inStrip hp⟩
    rw [← horizontalProjection_eq_Icc hK.isCap.nonempty hK.isCap.isCompact hK.isCap.convex]
    exact ⟨p, hp, rfl⟩
  obtain ⟨level, coefficient, U, hlevel, hc, hrate, hU, _, hHausdorff⟩ :=
    AngularGrid.exists_selected_sequence hK (by linarith : -R ≤ R) hbox
  have hlevelTop : Tendsto level atTop atTop := tendsto_atTop_mono hlevel tendsto_id
  have hwidth : 0 < capWidth K := by linarith [hK.width_bounds.1, one_lt_M]
  exact AngularGrid.curvature_density_sharp_on_wing hK.isCap hU hHausdorff hlevelTop
    (fun n => (hc n).le) hrate hR (fun n => (hU n).inBox) hwidth haffine
    hA hB htop hperp ha hab hb

theorem IsFullCapMaximizer.curvature_restrict_le_source_density {K : Set Plane}
    (hK : IsFullCapMaximizer K) {m c A B a b : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K),
      capRoof K x = m * x + c)
    (hA : 0 ≤ A) (hB : B ≤ Real.pi) (htop : Real.pi / 2 ∉ Ioo A B)
    (hperp : ∀ t ∈ Ioo A B, Real.cos t + m * Real.sin t ≠ 0)
    (ha : A < a) (hab : a ≤ b) (hb : b < B) :
    (upperCurvature K).restrict (Ioo a b) ≤
      (volume.restrict (Ioo a b)).withDensity
        (fun t => ENNReal.ofReal (sourceKappa (upperCornerVelocity K t))) := by
  obtain ⟨ρ, _, hρ, _, heq⟩ := hK.curvature_density_sharp_on_wing haffine
    hA hB htop hperp ha hab hb
  rw [heq]
  exact withDensity_mono (Eventually.of_forall (fun t => ENNReal.ofReal_le_ofReal (hρ t).2))

end AmbidextrousSofa
