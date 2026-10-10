import AmbidextrousSofa.Analysis.VisibleGraphFlux
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

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
  have hright : Tendsto d atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hd, Eventually.of_forall hdpos⟩
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
    hf.tendsto_slope_zero_right.comp hright

theorem measureReal_Ioc_eq_intervalIntegral_of_density
    {μ : Measure ℝ} {ρ : ℝ → ℝ} {S : Set ℝ} {a b : ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (heq : μ.restrict S = (volume.restrict S).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hab : a ≤ b) (hsub : Ioc a b ⊆ S) :
    μ.real (Ioc a b) = ∫ x in a..b, ρ x := by
  rw [intervalIntegral.integral_of_le hab]
  exact measureReal_eq_integral_of_restrict_withDensity hρ hρ0 heq measurableSet_Ioc hsub

theorem measureReal_Ioc_increment_tendsto_zero_of_density
    {μ : Measure ℝ} {ρ : ℝ → ℝ} {S : Set ℝ} {C x : ℝ} {d : ℕ → ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρC : ∀ y, ρ y ≤ C)
    (heq : μ.restrict S = (volume.restrict S).withDensity (fun y => ENNReal.ofReal (ρ y)))
    (hd : Tendsto d atTop (𝓝 0)) (hdpos : ∀ n, 0 < d n)
    (hsub : ∀ᶠ n in atTop, Ioc x (x + d n) ⊆ S) :
    Tendsto (fun n => μ.real (Ioc x (x + d n))) atTop (𝓝 0) := by
  have hcont : Continuous (fun y => ∫ z in x..y, ρ z) :=
    intervalIntegral.continuous_primitive (intervalIntegrable_bounded_real_density hρ hρ0 hρC) x
  have hi : Tendsto (fun n => ∫ z in x..(x + d n), ρ z) atTop (𝓝 0) := by
    simpa only [add_zero, intervalIntegral.integral_same] using
      hcont.continuousAt.tendsto.comp (tendsto_const_nhds.add hd)
  apply hi.congr'
  filter_upwards [hsub] with n hn
  exact (measureReal_Ioc_eq_intervalIntegral_of_density hρ hρ0 heq
    (by linarith [hdpos n]) hn).symm

theorem measureReal_Ioc_increment_div_tendsto_of_density
    {μ : Measure ℝ} {ρ : ℝ → ℝ} {S : Set ℝ} {x : ℝ} {d : ℕ → ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (heq : μ.restrict S = (volume.restrict S).withDensity (fun y => ENNReal.ofReal (ρ y)))
    (hLebesgue : HasDerivAt (fun y => ∫ z in x..y, ρ z) (ρ x) x)
    (hd : Tendsto d atTop (𝓝 0)) (hdpos : ∀ n, 0 < d n)
    (hsub : ∀ᶠ n in atTop, Ioc x (x + d n) ⊆ S) :
    Tendsto (fun n => μ.real (Ioc x (x + d n)) / d n) atTop (𝓝 (ρ x)) := by
  have hi := hLebesgue.forward_increment_div_tendsto hd hdpos
  simp only [intervalIntegral.integral_same, sub_zero] at hi
  apply hi.congr'
  filter_upwards [hsub] with n hn
  rw [measureReal_Ioc_eq_intervalIntegral_of_density hρ hρ0 heq
    (by linarith [hdpos n]) hn]

/-- This is the pointwise differentiation step at actual tangency and
Lebesgue points. All positive-height and angle-localization hypotheses
used by the graph flux are obtained on a genuine neighborhood. -/
theorem IsFullCapMaximizer.companion_density_ge_visible_corner
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C c b₀ t : ℝ}
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = c)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hb₀ : 0 ≤ b₀)
    (hcompanion : ∀ᵐ u ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ (u + Real.pi / 2) ≤ 1)
    (hfuture : ∀ᵐ u ∂volume.restrict (Ioo b₀ (Real.pi / 2)), ρ u ≤ 1)
    (ht : t ∈ Ioo b₀ (Real.pi / 2))
    (hq : 0 < firstCornerVelocity U t) (hr : 0 < secondCornerVelocity U t)
    (hDy : ∀ u ∈ Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ (secondTangency U u).2)
    (hcy : 0 < (attachedCorner U t).2)
    (hleft : horizontalLeft U + capWidth U / 4 ≤ (secondTangency U t).1)
    (hright : (attachedCorner U t).1 ≤ horizontalRight U - capWidth U / 4)
    (hDx : HasDerivAt (fun u => (secondTangency U u).1)
      ((1 - ρ (t + Real.pi / 2)) * Real.cos t) t)
    (hDy' : HasDerivAt (fun u => (secondTangency U u).2)
      ((1 - ρ (t + Real.pi / 2)) * Real.sin t) t)
    (hLebesgue : HasDerivAt (fun y => ∫ z in (t + Real.pi / 2)..y, ρ z)
      (ρ (t + Real.pi / 2)) (t + Real.pi / 2)) :
    1 + secondCornerVelocity U t ≤ 2 * ρ (t + Real.pi / 2) := by
  have htq : t ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨hb₀.trans_lt ht.1, ht.2⟩
  have htreg : t ∈ regularCornerDomain 0 := by simpa only [regularCornerDomain_zero] using htq
  have hvelocity := hU.isCap.continuousAt_cornerVelocities_on_regularCornerDomain
    hρ hρ0 hρC heq htreg
  have hcorner := hU.isCap.hasDerivAt_corner_coordinates_on_regularCornerDomain
    hρ hρ0 hρC heq htreg
  let P : Set ℝ := {u | u ∈ Ioo b₀ (Real.pi / 2) ∧
    0 < firstCornerVelocity U u ∧ 0 < secondCornerVelocity U u ∧
      0 < (attachedCorner U u).2}
  have hP : P ∈ 𝓝 t := by
    filter_upwards [isOpen_Ioo.mem_nhds ht,
      hvelocity.1.tendsto.eventually (isOpen_Ioi.mem_nhds hq),
      hvelocity.2.tendsto.eventually (isOpen_Ioi.mem_nhds hr),
      hcorner.2.continuousAt.tendsto.eventually (isOpen_Ioi.mem_nhds hcy)]
      with u hu hqu hru hcu
    exact ⟨hu, hqu, hru, hcu⟩
  obtain ⟨a, b, htI, hIP⟩ := mem_nhds_iff_exists_Ioo_subset.mp hP
  let d := AngularGrid.selectionRate
  have hd : Tendsto d atTop (𝓝 0) := AngularGrid.selectionRate_tendsto
  have hdpos : ∀ n, 0 < d n := AngularGrid.selectionRate_pos
  have hsmall : ∀ᶠ n in atTop, ∀ u ∈ Icc t (t + d n), u ∈ P := by
    filter_upwards [hd.eventually (isOpen_Iio.mem_nhds (sub_pos.mpr htI.2))] with n hn u hu
    apply hIP
    exact ⟨htI.1.trans_le hu.1, by linarith [hu.2]⟩
  have hbase : ∀ᶠ n in atTop, Ioc t (t + d n) ⊆ regularCurvatureDomain 0 := by
    filter_upwards [hsmall] with n hn u hu
    have huq : u ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨hb₀.trans_lt (hn u (Ioc_subset_Icc_self hu)).1.1, (hn u (Ioc_subset_Icc_self hu)).1.2⟩
    have hureg : u ∈ regularCornerDomain 0 := by simpa only [regularCornerDomain_zero] using huq
    exact hureg.2.1
  have hshift : ∀ᶠ n in atTop,
      Ioc (t + Real.pi / 2) (t + Real.pi / 2 + d n) ⊆ regularCurvatureDomain 0 := by
    filter_upwards [hsmall] with n hn u hu
    have huI : u - Real.pi / 2 ∈ Icc t (t + d n) := by
      constructor <;> linarith [hu.1, hu.2]
    have huq : u - Real.pi / 2 ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨hb₀.trans_lt (hn _ huI).1.1, (hn _ huI).1.2⟩
    have hureg : u - Real.pi / 2 ∈ regularCornerDomain 0 := by
      simpa only [regularCornerDomain_zero] using huq
    simpa only [sub_add_cancel] using hureg.2.2
  have hmass0 := measureReal_Ioc_increment_tendsto_zero_of_density hρ hρ0 hρC heq hd hdpos hbase
  have hmassShift0 := measureReal_Ioc_increment_tendsto_zero_of_density hρ hρ0 hρC heq hd hdpos hshift
  have hquot := measureReal_Ioc_increment_div_tendsto_of_density
    hρ hρ0 heq hLebesgue hd hdpos hshift
  have hDxlim := hDx.forward_increment_div_tendsto hd hdpos
  have hDylim := hDy'.forward_increment_div_tendsto hd hdpos
  have hcxlim := hcorner.1.forward_increment_div_tendsto hd hdpos
  have hcylim := hcorner.2.forward_increment_div_tendsto hd hdpos
  let Q : ℕ → ℝ := fun n =>
    (Real.cos t * ((secondTangency U (t + d n)).1 - (secondTangency U t).1) +
      Real.sin t * ((secondTangency U (t + d n)).2 - (secondTangency U t).2) +
      (Real.cos t * ((attachedCorner U t).1 - (attachedCorner U (t + d n)).1) +
        Real.sin t * ((attachedCorner U t).2 - (attachedCorner U (t + d n)).2))) / d n
  have hQ : Tendsto Q atTop (𝓝 (1 - ρ (t + Real.pi / 2) + secondCornerVelocity U t)) := by
    have hlim := ((hDxlim.const_mul (Real.cos t)).add (hDylim.const_mul (Real.sin t))).sub
      ((hcxlim.const_mul (Real.cos t)).add (hcylim.const_mul (Real.sin t)))
    convert hlim using 1
    · ext n
      dsimp only [Q]
      ring
    · dsimp only [cornerVelocityX, cornerVelocityY]
      nlinarith [congrArg (fun z : ℝ => (1 - ρ (t + Real.pi / 2)) * z)
        (Real.sin_sq_add_cos_sq t),
        congrArg (fun z : ℝ => secondCornerVelocity U t * z) (Real.sin_sq_add_cos_sq t)]
  have hbound : ∀ᶠ n in atTop, Q n ≤
      (upperCurvature U).real (Ioc (t + Real.pi / 2) (t + Real.pi / 2 + d n)) / d n +
        (upperCurvature U).real (Ioc (t + Real.pi / 2) (t + Real.pi / 2 + d n)) +
          (upperCurvature U).real (Ioc t (t + d n)) := by
    filter_upwards [hsmall] with n hn
    have hflux := hU.visible_tangency_corner_flux hheight haffine hρ hρ0 hρC heq hb₀
      hcompanion hfuture (by linarith [hdpos n] : t < t + d n)
      (show t ∈ Icc t (t + d n) from ⟨le_rfl, by linarith [hdpos n]⟩)
      (fun u hu => (hn u hu).1) (fun u hu => (hn u hu).2.1)
      (fun u hu => (hn u hu).2.2.1)
      (fun u hu => hDy u ⟨hb₀.trans_lt (hn u hu).1.1, (hn u hu).1.2⟩)
      (fun u hu => (hn u hu).2.2.2) hleft hright
    have hdiv := div_le_div_of_nonneg_right hflux (hdpos n).le
    have hcomm : t + d n + Real.pi / 2 = t + Real.pi / 2 + d n := by ring
    simpa only [hcomm, add_sub_cancel_left, add_div, mul_div_cancel_left₀ _ (hdpos n).ne',
      Q, add_assoc] using hdiv
  have hfinal := le_of_tendsto_of_tendsto hQ
    (by simpa only [add_zero] using (hquot.add hmassShift0).add hmass0) hbound
  linarith

/-- All differentiation hypotheses in the visible companion law hold
almost everywhere for the actual bounded curvature density. -/
theorem IsFullCapMaximizer.ae_companion_density_ge_visible_corner
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C c b₀ : ℝ}
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = c)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρC : ∀ x, ρ x ≤ C)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hb₀ : 0 ≤ b₀)
    (hcompanion : ∀ᵐ u ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ (u + Real.pi / 2) ≤ 1)
    (hfuture : ∀ᵐ u ∂volume.restrict (Ioo b₀ (Real.pi / 2)), ρ u ≤ 1)
    (hDy : ∀ u ∈ Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ (secondTangency U u).2) :
    ∀ᵐ t ∂volume.restrict (Ioo b₀ (Real.pi / 2)),
      0 < firstCornerVelocity U t → 0 < secondCornerVelocity U t →
      0 < (attachedCorner U t).2 →
      horizontalLeft U + capWidth U / 4 ≤ (secondTangency U t).1 →
      (attachedCorner U t).1 ≤ horizontalRight U - capWidth U / 4 →
        1 + secondCornerVelocity U t ≤ 2 * ρ (t + Real.pi / 2) := by
  have hlocal : LocallyIntegrable ρ volume := by
    apply locallyIntegrable_iff.mpr
    intro K hK
    apply IntegrableOn.of_bound hK.measure_lt_top hρ.aestronglyMeasurable C
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hρ0 x)]
      exact hρC x)
  have hLeb := (measurePreserving_add_right volume (Real.pi / 2)).quasiMeasurePreserving.ae
    hlocal.ae_hasDerivAt_integral
  have hTang := hU.isCap.ae_hasDerivAt_tangency_coordinates_on_regularCornerDomain
    hρ hρ0 hρC heq
  rw [regularCornerDomain_zero] at hTang
  have hTang' := ae_restrict_of_ae_restrict_of_subset
    (show Ioo b₀ (Real.pi / 2) ⊆ Ioo (0 : ℝ) (Real.pi / 2) from
      fun _ ht => ⟨hb₀.trans_lt ht.1, ht.2⟩) hTang
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hTang', ae_restrict_of_ae hLeb]
    with t ht hT hL
  intro hq hr hcy hleft hright
  exact hU.companion_density_ge_visible_corner hheight haffine hρ hρ0 hρC heq hb₀
    hcompanion hfuture ht hq hr hDy hcy hleft hright hT.2.2.1 hT.2.2.2 (hL _)

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
  have hfloor : ∀ u ∈ Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ (secondTangency U u).2 :=
    fun u hu => (hU.secondTangency_from_top_endpoint hheight hmiddle hρ hρ0 hρC heq hcompanion hu).2
  have hflux := hU.ae_companion_density_ge_visible_corner hheight hmiddle hρ hρ0 hρC heq hb₀
    hcompanion hfuture hfloor
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hflux] with t ht hf
  intro hq hr
  have hgeometry := hU.visible_corner_middle_and_height hheight hmiddle hρ hρ0 hρC heq hb₀
    hcompanion hfuture ht hq hr
  exact hf hq hr hgeometry.2.2 hgeometry.1 hgeometry.2.1

end AmbidextrousSofa
