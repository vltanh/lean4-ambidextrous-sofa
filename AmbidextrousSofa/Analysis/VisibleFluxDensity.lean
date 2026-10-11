module

public import AmbidextrousSofa.Analysis.VisibleGraphFlux
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

@[expose] public section

/-!
# The actual companion density lower bound on visible positive corners

The two physical graph projections are differentiated after the finite
source limit has been proved. Local curvature masses tend to zero, while
the companion interval mass divided by its width tends to the actual
companion density at its Lebesgue points. The resulting inequality is
`1 + secondCornerVelocity ≤ 2 * companion density`.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem HasDerivAt.forward_increment_div_tendsto
    {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x)
    {d : ℕ → ℝ} (hd : Tendsto d atTop (𝓝 0)) (hdpos : ∀ n, 0 < d n) :
    Tendsto (fun n => (f (x + d n) - f x) / d n) atTop (𝓝 f') := by
  simpa only [Function.comp_def, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    hf.tendsto_slope_zero_right.comp (tendsto_nhdsWithin_iff.mpr ⟨hd, .of_forall hdpos⟩)

theorem measureReal_Ioc_eq_intervalIntegral_of_density
    {μ : Measure ℝ} {ρ : ℝ → ℝ} {S : Set ℝ} {a b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (heq : μ.restrict S = (volume.restrict S).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hab : a ≤ b) (hsub : Ioc a b ⊆ S) :
    μ.real (Ioc a b) = ∫ x in a..b, ρ x :=
  (measureReal_eq_integral_of_restrict_withDensity hρ hρ0 heq measurableSet_Ioc hsub).trans
    (intervalIntegral.integral_of_le hab).symm

theorem measureReal_Ioc_increment_tendsto_zero_of_density
    {μ : Measure ℝ} {ρ : ℝ → ℝ} {S : Set ℝ} {C x : ℝ} {d : ℕ → ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρC : ∀ y, ρ y ≤ C)
    (heq : μ.restrict S = (volume.restrict S).withDensity (fun y => ENNReal.ofReal (ρ y)))
    (hd : Tendsto d atTop (𝓝 0)) (hdpos : ∀ n, 0 < d n)
    (hsub : ∀ᶠ n in atTop, Ioc x (x + d n) ⊆ S) :
    Tendsto (fun n => μ.real (Ioc x (x + d n))) atTop (𝓝 0) := by
  refine (((intervalIntegral.continuous_primitive (intervalIntegrable_bounded_real_density
    hρ hρ0 hρC) x).tendsto' (x + 0) 0 (by simp)).comp (tendsto_const_nhds.add hd)).congr' ?_
  filter_upwards [hsub] with n hn
  exact (measureReal_Ioc_eq_intervalIntegral_of_density hρ hρ0 heq
    (le_add_of_nonneg_right (hdpos n).le) hn).symm

theorem measureReal_Ioc_increment_div_tendsto_of_density
    {μ : Measure ℝ} {ρ : ℝ → ℝ} {S : Set ℝ} {x : ℝ} {d : ℕ → ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (heq : μ.restrict S = (volume.restrict S).withDensity (fun y => ENNReal.ofReal (ρ y)))
    (hLebesgue : HasDerivAt (fun y => ∫ z in x..y, ρ z) (ρ x) x)
    (hd : Tendsto d atTop (𝓝 0)) (hdpos : ∀ n, 0 < d n)
    (hsub : ∀ᶠ n in atTop, Ioc x (x + d n) ⊆ S) :
    Tendsto (fun n => μ.real (Ioc x (x + d n)) / d n) atTop (𝓝 (ρ x)) := by
  have hi := HasDerivAt.forward_increment_div_tendsto hLebesgue hd hdpos
  simp only [intervalIntegral.integral_same, sub_zero] at hi
  refine hi.congr' ?_
  filter_upwards [hsub] with n hn
  rw [measureReal_Ioc_eq_intervalIntegral_of_density hρ hρ0 heq
    (le_add_of_nonneg_right (hdpos n).le) hn]

/-- The actual horizontal top endpoints discharge the height and middle
containment of both visible graph pieces. Zero-height tangency pieces
are included through the proved angular order inequality. -/
theorem IsFullCapMaximizer.ae_companion_density_ge_of_unit_companion_and_future
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C b₀ : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hb₀ : 0 ≤ b₀)
    (hcompanion : ∀ᵐ u ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ (u + Real.pi / 2) ≤ 1)
    (hfuture : ∀ᵐ u ∂volume.restrict (Ioo b₀ (Real.pi / 2)), ρ u ≤ 1) :
    ∀ᵐ t ∂volume.restrict (Ioo b₀ (Real.pi / 2)),
      0 < firstCornerVelocity U t → 0 < secondCornerVelocity U t →
        1 + secondCornerVelocity U t ≤ 2 * ρ (t + Real.pi / 2) := by
  -- Almost every `t` is a point of differentiability of the second tangency and a Lebesgue
  -- point of `ρ` at `t + π / 2`.
  have hlocal : LocallyIntegrable ρ volume := locallyIntegrable_iff.2 fun K hK =>
    IntegrableOn.of_bound hK.measure_lt_top hρ.aestronglyMeasurable C
      (.of_forall fun x => (Real.norm_of_nonneg (hρ0 x)).trans_le (hρC x))
  have hTang := hU.isCap.ae_hasDerivAt_tangency_coordinates_on_regularCornerDomain
    hρ hρ0 hρC heq
  rw [regularCornerDomain_zero] at hTang
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_left hb₀) hTang,
    ae_restrict_of_ae ((measurePreserving_add_right volume (Real.pi / 2)).quasiMeasurePreserving.ae
      (LocallyIntegrable.ae_hasDerivAt_integral hlocal))] with t ht hT hL hq hr
  obtain ⟨hleft, hright, hcy⟩ := hU.visible_corner_middle_and_height hheight hmiddle hρ hρ0 hρC
    heq hb₀ hcompanion hfuture ht hq hr
  have htreg := regularCornerDomain_zero.ge (Ioo_subset_Ioo_left hb₀ ht)
  have hvelocity := hU.isCap.continuousAt_cornerVelocities_on_regularCornerDomain
    hρ hρ0 hρC heq htreg
  have hcorner := hU.isCap.hasDerivAt_corner_coordinates_on_regularCornerDomain
    hρ hρ0 hρC heq htreg
  -- On a neighborhood `(a, b)` of `t` all the localization hypotheses of the graph flux hold.
  obtain ⟨a, b, htI, hIP⟩ := mem_nhds_iff_exists_Ioo_subset.mp (Filter.Eventually.and
    (isOpen_Ioo.mem_nhds ht) ((hvelocity.1.tendsto.eventually (lt_mem_nhds hq)).and
      ((hvelocity.2.tendsto.eventually (lt_mem_nhds hr)).and
        (hcorner.2.continuousAt.tendsto.eventually (lt_mem_nhds hcy)))))
  obtain ⟨d, hd, hdpos⟩ : ∃ d : ℕ → ℝ, Tendsto d atTop (𝓝 0) ∧ ∀ n, 0 < d n :=
    ⟨_, AngularGrid.selectionRate_tendsto, AngularGrid.selectionRate_pos⟩
  have hsmall : ∀ᶠ n in atTop, Icc t (t + d n) ⊆ Ioo a b :=
    (hd.eventually (gt_mem_nhds (sub_pos.2 htI.2))).mono fun n hn =>
      Icc_subset_Ioo htI.1 (by linarith)
  have hdirs : ∀ᶠ n in atTop, Icc t (t + d n) ⊆ regularCurvatureDomain 0 ∧
      Icc (t + Real.pi / 2) (t + d n + Real.pi / 2) ⊆ regularCurvatureDomain 0 :=
    hsmall.mono fun n hn => regularCornerDomain_interval_directions fun u hu =>
      regularCornerDomain_zero.ge (Ioo_subset_Ioo_left hb₀ (hIP (hn hu)).1)
  have hshift : ∀ᶠ n in atTop,
      Ioc (t + Real.pi / 2) (t + Real.pi / 2 + d n) ⊆ regularCurvatureDomain 0 :=
    hdirs.mono fun n hn => by rw [add_right_comm t]; exact Ioc_subset_Icc_self.trans hn.2
  -- Divide the graph flux bound on `[t, t + d n]` by `d n` and let `n → ∞`.
  have key := le_of_tendsto_of_tendsto
    ((((HasDerivAt.forward_increment_div_tendsto hT.2.2.1 hd hdpos).const_mul (Real.cos t)).add
      ((HasDerivAt.forward_increment_div_tendsto hT.2.2.2 hd hdpos).const_mul (Real.sin t))).sub
      (((HasDerivAt.forward_increment_div_tendsto hcorner.1 hd hdpos).const_mul (Real.cos t)).add
        ((HasDerivAt.forward_increment_div_tendsto hcorner.2 hd hdpos).const_mul (Real.sin t))))
    (((measureReal_Ioc_increment_div_tendsto_of_density hρ hρ0 heq (hL _) hd hdpos
      hshift).add (measureReal_Ioc_increment_tendsto_zero_of_density hρ hρ0 hρC heq hd hdpos
        hshift)).add (measureReal_Ioc_increment_tendsto_zero_of_density hρ hρ0 hρC heq hd hdpos
          (hdirs.mono fun n hn => Ioc_subset_Icc_self.trans hn.1))) ?_
  · simp only [cornerVelocityX, cornerVelocityY, add_zero] at key
    linarith [congrArg ((1 - ρ (t + Real.pi / 2)) * ·) (Real.sin_sq_add_cos_sq t),
      congrArg (secondCornerVelocity U t * ·) (Real.sin_sq_add_cos_sq t)]
  filter_upwards [hsmall] with n hn
  have hdn := hdpos n
  have hflux := hU.visible_tangency_corner_flux hheight hmiddle hρ hρ0 hρC heq hb₀
    hcompanion hfuture (lt_add_of_pos_right t hdn) (left_mem_Icc.2 (le_add_of_nonneg_right hdn.le))
    (fun u hu => (hIP (hn hu)).1) (fun u hu => (hIP (hn hu)).2.1) (fun u hu => (hIP (hn hu)).2.2.1)
    (fun u hu => (hU.secondTangency_from_top_endpoint hheight hmiddle hρ hρ0 hρC heq hcompanion
      (Ioo_subset_Ioo_left hb₀ (hIP (hn hu)).1)).2)
    (fun u hu => (hIP (hn hu)).2.2.2) hleft hright
  rw [add_right_comm t (d n)] at hflux
  convert div_le_div_of_nonneg_right hflux hdn.le using 1
  · ring
  · field_simp
    ring

end AmbidextrousSofa
