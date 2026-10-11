module

public import AmbidextrousSofa.Analysis.MovingSupportSecants
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import AmbidextrousSofa.Analysis.SurfaceAreaFacts

@[expose] public section

/-!
# Actual corner velocities and the sharp finite-density limit

The two corner velocities use the right support derivative of the actual
cap. At every non-atomic companion normal, the shrinking sampled secants
converge to these velocities even when the cap and sample normal move.
The exact neighboring-wall expression, divided by the angular mesh,
then converges to `max |q| ((|q| + 1) / 2)`.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

def sourceKappa (q : ℝ) : ℝ := max |q| ((|q| + 1) / 2)

theorem sourceKappa_nonneg (q : ℝ) : 0 ≤ sourceKappa q :=
  (abs_nonneg q).trans (le_max_left _ _)

theorem sourceKappa_neg (q : ℝ) : sourceKappa (-q) = sourceKappa q := by
  simp only [sourceKappa, abs_neg]

theorem continuous_sourceKappa : Continuous sourceKappa := by
  unfold sourceKappa; fun_prop

open MovingSofaOptimality in
def firstCornerVelocity (U : Set Plane) (t : ℝ) : ℝ :=
  supp U t + dot (vplus U (t + Real.pi / 2)) (vvec (t + Real.pi / 2)) - 1

open MovingSofaOptimality in
def secondCornerVelocity (U : Set Plane) (t : ℝ) : ℝ :=
  supp U (t + Real.pi / 2) - dot (vplus U t) (vvec t) - 1

theorem firstCornerVelocity_eq_gPlus (U : Set Plane) (t : ℝ) :
    firstCornerVelocity U t = MovingSofaOptimality.gPlus U t - 1 := by
  rw [MovingSofaOptimality.inj_gPlus_eq]; rfl

theorem secondCornerVelocity_eq_fPlus (U : Set Plane) (t : ℝ) :
    secondCornerVelocity U t = MovingSofaOptimality.fPlus U t - 1 := by
  rw [MovingSofaOptimality.inj_fPlus_eq]; rfl

open MovingSofaOptimality in
theorem IsDownwardCap.measurable_supportTangent {U : Set Plane} (hU : IsDownwardCap U) :
    Measurable (fun t => dot (vplus U t) (vvec t)) :=
  continuous_dot_pair.measurable.comp
    ((AmbidextrousSofa.measurable_vplus hU.imported_isConvexBody).prodMk continuous_vvec.measurable)

/-- The source paired with an upper normal lies a quarter-turn away. -/
def companionSourceAngle (t : ℝ) : ℝ :=
  if t < Real.pi / 2 then t + Real.pi / 2 else t - Real.pi / 2

def upperCornerVelocity (U : Set Plane) (t : ℝ) : ℝ :=
  if t < Real.pi / 2 then firstCornerVelocity U t
    else secondCornerVelocity U (t - Real.pi / 2)

theorem IsDownwardCap.measurable_upperCornerVelocity {U : Set Plane} (hU : IsDownwardCap U) :
    Measurable (upperCornerVelocity U) := by
  have hs := hU.imported_isConvexBody.continuous_supp.measurable
  have hv := hU.measurable_supportTangent
  exact ((hs.add (hv.comp (measurable_add_const _))).sub_const 1).ite measurableSet_Iio
    ((((hs.comp (measurable_add_const _)).sub hv).sub_const 1).comp (measurable_sub_const _))

theorem ae_sigmaAt_companionSourceAngle_eq_zero (U : Set Plane) :
    ∀ᵐ t : ℝ, MovingSofaOptimality.sigmaAt U (companionSourceAngle t) = 0 := by
  have h (c : ℝ) : ∀ᵐ t : ℝ, MovingSofaOptimality.sigmaAt U (t + c) = 0 := by
    filter_upwards [((MovingSofaOptimality.countable_sigma_singleton_ne U).preimage
      (add_left_injective c)).ae_notMem volume] with t ht
    simp_all [MovingSofaOptimality.sigmaAt]
  filter_upwards [h (Real.pi / 2), h (-(Real.pi / 2))] with t hp hm
  unfold companionSourceAngle; split_ifs <;> simpa [sub_eq_add_neg]

namespace AngularGrid

theorem tan_div_self_tendsto {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0))
    (hpos : ∀ n, 0 < δ n) :
    Tendsto (fun n => Real.tan (δ n) / δ n) atTop (𝓝 1) := by
  have hderiv : HasDerivAt Real.tan 1 0 := by
    simpa only [Real.cos_zero, one_pow, div_one] using Real.hasDerivAt_tan (x := 0) (by simp)
  simpa only [zero_add, Real.tan_zero, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm,
    Function.comp_def] using hderiv.tendsto_slope_zero_right.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hδ, Eventually.of_forall hpos⟩)

theorem finiteCurvatureDensity_div_tendsto {q δ : ℕ → ℝ} {v : ℝ}
    (hq : Tendsto q atTop (𝓝 v)) (hδ : Tendsto δ atTop (𝓝 0))
    (hpos : ∀ n, 0 < δ n) :
    Tendsto (fun n => finiteCurvatureDensity (q n) (δ n) / δ n) atTop
      (𝓝 (sourceKappa v)) := by
  have hhalf : Tendsto (fun n => δ n / 2) atTop (𝓝 0) := by simpa using hδ.div_const 2
  have htan : Tendsto (fun n => Real.tan (δ n / 2)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuousAt_tan.2 (by simp)).tendsto.comp hhalf
  have hA := (tan_div_self_tendsto hδ hpos).mul (hq.abs.add htan)
  convert hA.max ((hA.add (tan_div_self_tendsto hhalf fun n => half_pos (hpos n))).div_const 2)
    using 2 with n
  · rw [finiteCurvatureDensity, ← max_div_div_right (hpos n).le]
    congr 1 <;> ring
  · simp [sourceKappa]

end AngularGrid

section Secants

variable {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
  (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
  (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
include h hU hK hB hbox

theorem CapHausdorffTendsto.firstCornerSecant_tendsto
    {angle δ : ℕ → ℝ} {t : ℝ} (hangle : Tendsto angle atTop (𝓝 t))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hsin : ∀ n, 0 < Real.sin (δ n)) (hcos : ∀ n, 0 ≤ Real.cos (δ n))
    (ht : MovingSofaOptimality.sigmaAt K (t + Real.pi / 2) = 0) :
    Tendsto (fun n => AngularGrid.firstCornerSecant (U n) (angle n) (δ n)) atTop
      (𝓝 (firstCornerVelocity K t)) := by
  refine (((h.support_tendsto_moving hU hK ((continuous_unitNormal.tendsto t).comp hangle)).add
    (h.forwardAngularSecant_tendsto hU hK hB hbox (hangle.add_const (Real.pi / 2)) hδ hsin hcos
      ht)).sub_const 1).congr fun n => ?_
  simp only [AngularGrid.firstCornerSecant, forwardAngularSecant, companionNormal_eq_unitNormal,
    add_right_comm _ (δ n)]
  rfl

theorem CapHausdorffTendsto.secondCornerSecant_tendsto
    {angle δ : ℕ → ℝ} {t : ℝ} (hangle : Tendsto angle atTop (𝓝 t))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hsin : ∀ n, 0 < Real.sin (δ n)) (hcos : ∀ n, 0 ≤ Real.cos (δ n))
    (ht : MovingSofaOptimality.sigmaAt K t = 0) :
    Tendsto (fun n => AngularGrid.secondCornerSecant (U n) (angle n) (δ n)) atTop
      (𝓝 (secondCornerVelocity K t)) := by
  refine (((h.support_tendsto_moving hU hK ((continuous_unitNormal.tendsto _).comp
    (hangle.add_const (Real.pi / 2)))).sub
    (h.backwardAngularSecant_tendsto hU hK hB hbox hangle hδ hsin hcos ht)).sub_const 1).congr
    fun n => ?_
  simp only [AngularGrid.secondCornerSecant, backwardAngularSecant, companionNormal_eq_unitNormal,
    Function.comp_apply, ← angleSupport.eq_1, angleSupport_eq_imported_supp]
  ring

/-- The sampled source may change at every stage. Its moving full normal
is the only angular convergence hypothesis. -/
theorem AngularGrid.cornerSecant_tendsto
    {level : ℕ → ℕ} (hlevel : Tendsto level atTop atTop)
    (j : ∀ n, SourceIndex (dyadic (level n))) {t : ℝ}
    (hangle : Tendsto (fun n => fullAngle (dyadic (level n)) (j n)) atTop (𝓝 t))
    (htop : t ≠ Real.pi / 2)
    (ht : MovingSofaOptimality.sigmaAt K (companionSourceAngle t) = 0) :
    Tendsto (fun n => cornerSecant (U n) (level n) (j n)) atTop
      (𝓝 (upperCornerVelocity K t)) := by
  have hs n := mesh_sin_pos (level n)
  have hc n := (mesh_cos_pos (level n)).le
  unfold companionSourceAngle at ht
  unfold upperCornerVelocity
  split_ifs at ht ⊢ with hleft
  · refine (h.firstCornerSecant_tendsto hU hK hB hbox hangle (mesh_tendsto.comp hlevel) hs hc
      ht).congr' ?_
    filter_upwards [hangle.eventually (gt_mem_nhds hleft)] with n hn
    rcases hj : j n with s | s
    · rfl
    · simp only [hj, fullAngle] at hn
      linarith [(interiorPoint_mem (dyadic (level n)) s).1]
  · refine (h.secondCornerSecant_tendsto hU hK hB hbox (hangle.sub_const _)
      (mesh_tendsto.comp hlevel) hs hc ht).congr' ?_
    filter_upwards [hangle.eventually (lt_mem_nhds (lt_of_le_of_ne (not_lt.1 hleft) htop.symm))]
      with n hn
    rcases hj : j n with s | s
    · simp only [hj, fullAngle] at hn
      linarith [(interiorPoint_mem (dyadic (level n)) s).2]
    · simp [cornerSecant, fullAngle]

theorem AngularGrid.sampledCurvatureDensity_tendsto
    {level : ℕ → ℕ} (hlevel : Tendsto level atTop atTop)
    (j : ∀ n, SourceIndex (dyadic (level n))) {t : ℝ}
    (hangle : Tendsto (fun n => fullAngle (dyadic (level n)) (j n)) atTop (𝓝 t))
    (htop : t ≠ Real.pi / 2)
    (ht : MovingSofaOptimality.sigmaAt K (companionSourceAngle t) = 0) :
    Tendsto (fun n => finiteCurvatureDensity (cornerSecant (U n) (level n) (j n))
      (mesh (level n)) / mesh (level n)) atTop (𝓝 (sourceKappa (upperCornerVelocity K t))) :=
  finiteCurvatureDensity_div_tendsto
    (cornerSecant_tendsto h hU hK hB hbox hlevel j hangle htop ht)
    (mesh_tendsto.comp hlevel) (fun n => mesh_pos (level n))

end Secants

end AmbidextrousSofa
