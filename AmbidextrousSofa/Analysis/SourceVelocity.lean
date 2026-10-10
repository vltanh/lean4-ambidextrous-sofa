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
  unfold sourceKappa
  fun_prop

def firstCornerVelocity (U : Set Plane) (t : ℝ) : ℝ :=
  MovingSofaOptimality.supp U t +
    MovingSofaOptimality.dot (MovingSofaOptimality.vplus U (t + Real.pi / 2)) (MovingSofaOptimality.vvec (t + Real.pi / 2)) - 1

def secondCornerVelocity (U : Set Plane) (t : ℝ) : ℝ :=
  MovingSofaOptimality.supp U (t + Real.pi / 2) -
    MovingSofaOptimality.dot (MovingSofaOptimality.vplus U t) (MovingSofaOptimality.vvec t) - 1

theorem firstCornerVelocity_eq_gPlus (U : Set Plane) (t : ℝ) :
    firstCornerVelocity U t = MovingSofaOptimality.gPlus U t - 1 := by
  rw [MovingSofaOptimality.inj_gPlus_eq]
  rfl

theorem secondCornerVelocity_eq_fPlus (U : Set Plane) (t : ℝ) :
    secondCornerVelocity U t = MovingSofaOptimality.fPlus U t - 1 := by
  rw [MovingSofaOptimality.inj_fPlus_eq]
  rfl

theorem IsDownwardCap.measurable_supportTangent {U : Set Plane} (hU : IsDownwardCap U) :
    Measurable (fun t => MovingSofaOptimality.dot (MovingSofaOptimality.vplus U t) (MovingSofaOptimality.vvec t)) :=
  MovingSofaOptimality.continuous_dot_pair.measurable.comp
    ((AmbidextrousSofa.measurable_vplus hU.imported_isConvexBody).prodMk
      MovingSofaOptimality.continuous_vvec.measurable)

theorem IsDownwardCap.measurable_firstCornerVelocity {U : Set Plane} (hU : IsDownwardCap U) :
    Measurable (firstCornerVelocity U) := by
  unfold firstCornerVelocity
  exact (hU.imported_isConvexBody.continuous_supp.measurable.add
    (hU.measurable_supportTangent.comp (measurable_id.add_const (Real.pi / 2)))).sub_const 1

theorem IsDownwardCap.measurable_secondCornerVelocity {U : Set Plane} (hU : IsDownwardCap U) :
    Measurable (secondCornerVelocity U) := by
  unfold secondCornerVelocity
  exact ((hU.imported_isConvexBody.continuous_supp.measurable.comp
    (measurable_id.add_const (Real.pi / 2))).sub hU.measurable_supportTangent).sub_const 1

/-- The source paired with an upper normal lies a quarter-turn away. -/
def companionSourceAngle (t : ℝ) : ℝ :=
  if t < Real.pi / 2 then t + Real.pi / 2 else t - Real.pi / 2

def upperCornerVelocity (U : Set Plane) (t : ℝ) : ℝ :=
  if t < Real.pi / 2 then firstCornerVelocity U t
    else secondCornerVelocity U (t - Real.pi / 2)

theorem IsDownwardCap.measurable_upperCornerVelocity {U : Set Plane} (hU : IsDownwardCap U) :
    Measurable (upperCornerVelocity U) :=
  Measurable.ite measurableSet_Iio hU.measurable_firstCornerVelocity
    (hU.measurable_secondCornerVelocity.comp (measurable_id.sub_const (Real.pi / 2)))

theorem ae_sigmaAt_add_eq_zero (U : Set Plane) (c : ℝ) :
    ∀ᵐ t : ℝ, MovingSofaOptimality.sigmaAt U (t + c) = 0 := by
  have hcount : {t : ℝ | MovingSofaOptimality.sigma U {t + c} ≠ 0}.Countable :=
    (MovingSofaOptimality.countable_sigma_singleton_ne U).preimage
      (f := fun t : ℝ => t + c) (by intro x y h; linarith)
  filter_upwards [hcount.ae_notMem volume] with t ht
  have hzero : MovingSofaOptimality.sigma U {t + c} = 0 := by
    simpa only [mem_setOf_eq, not_not] using ht
  simp only [MovingSofaOptimality.sigmaAt, hzero, ENNReal.toReal_zero]

theorem ae_sigmaAt_companionSourceAngle_eq_zero (U : Set Plane) :
    ∀ᵐ t : ℝ, MovingSofaOptimality.sigmaAt U (companionSourceAngle t) = 0 := by
  filter_upwards [ae_sigmaAt_add_eq_zero U (Real.pi / 2),
    ae_sigmaAt_add_eq_zero U (-(Real.pi / 2))] with t hp hm
  by_cases ht : t < Real.pi / 2
  · simpa only [companionSourceAngle, if_pos ht] using hp
  · simpa only [companionSourceAngle, if_neg ht, sub_eq_add_neg] using hm

namespace AngularGrid

theorem firstCornerSecant_eq_forward (U : Set Plane) (t δ : ℝ) :
    firstCornerSecant U t δ =
      MovingSofaOptimality.supp U t + forwardAngularSecant U (t + Real.pi / 2) δ - 1 := by
  simp only [firstCornerSecant, forwardAngularSecant, companionNormal_eq_unitNormal]
  change MovingSofaOptimality.supp U t +
    (MovingSofaOptimality.supp U ((t + δ) + Real.pi / 2) -
      MovingSofaOptimality.supp U (t + Real.pi / 2) * Real.cos δ) / Real.sin δ - 1 = _
  rw [show (t + δ) + Real.pi / 2 = (t + Real.pi / 2) + δ by ring]

theorem secondCornerSecant_eq_backward (U : Set Plane) (t δ : ℝ) :
    secondCornerSecant U t δ =
      MovingSofaOptimality.supp U (t + Real.pi / 2) - backwardAngularSecant U t δ - 1 := by
  simp only [secondCornerSecant, backwardAngularSecant, companionNormal_eq_unitNormal]
  change MovingSofaOptimality.supp U (t + Real.pi / 2) +
    (MovingSofaOptimality.supp U (t - δ) - MovingSofaOptimality.supp U t * Real.cos δ) / Real.sin δ - 1 = _
  ring

theorem tan_div_self_tendsto {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0))
    (hpos : ∀ n, 0 < δ n) :
    Tendsto (fun n => Real.tan (δ n) / δ n) atTop (𝓝 1) := by
  have hderiv : HasDerivAt Real.tan 1 0 := by
    simpa only [Real.cos_zero, one_pow, div_one] using
      (Real.hasDerivAt_tan (x := 0) (by simp))
  have hwithin : Tendsto δ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hδ, Eventually.of_forall hpos⟩
  simpa only [zero_add, Real.tan_zero, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm,
    Function.comp_def] using hderiv.tendsto_slope_zero_right.comp hwithin

theorem finiteCurvatureDensity_div_eq {q δ : ℝ} (hδ : 0 ≤ δ) :
    finiteCurvatureDensity q δ / δ =
      max ((Real.tan δ / δ) * (|q| + Real.tan (δ / 2)))
        (((Real.tan δ / δ) * (|q| + Real.tan (δ / 2)) +
          2 * (Real.tan (δ / 2) / δ)) / 2) := by
  rw [finiteCurvatureDensity, ← max_div_div_right hδ]
  congr 1 <;> ring

theorem finiteCurvatureDensity_div_tendsto {q δ : ℕ → ℝ} {v : ℝ}
    (hq : Tendsto q atTop (𝓝 v)) (hδ : Tendsto δ atTop (𝓝 0))
    (hpos : ∀ n, 0 < δ n) :
    Tendsto (fun n => finiteCurvatureDensity (q n) (δ n) / δ n) atTop
      (𝓝 (sourceKappa v)) := by
  have hratio := tan_div_self_tendsto hδ hpos
  have hhalf : Tendsto (fun n => δ n / 2) atTop (𝓝 0) := by
    simpa only [zero_div] using hδ.div_const 2
  have hhalfRatio := tan_div_self_tendsto hhalf (fun n => div_pos (hpos n) (by norm_num))
  have hhalfRatio' : Tendsto (fun n => Real.tan (δ n / 2) / δ n) atTop (𝓝 (1 / 2)) := by
    have h := hhalfRatio.div_const 2
    simpa only [div_div, div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using h
  have htan : Tendsto (fun n => Real.tan (δ n / 2)) atTop (𝓝 0) := by
    have hcont := (Real.hasDerivAt_tan (x := 0) (by simp)).continuousAt.tendsto
    simpa only [Real.tan_zero, Function.comp_def] using hcont.comp hhalf
  have hA := hratio.mul (hq.abs.add htan)
  have hB := (hA.add (hhalfRatio'.const_mul 2)).div_const 2
  have hmax := hA.max hB
  have heq (n : ℕ) := finiteCurvatureDensity_div_eq (q := q n) (hpos n).le
  simpa only [heq, one_mul, add_zero, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
    sourceKappa] using hmax

end AngularGrid

theorem CapHausdorffTendsto.firstCornerSecant_tendsto
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
    {angle δ : ℕ → ℝ} {t : ℝ} (hangle : Tendsto angle atTop (𝓝 t))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hsin : ∀ n, 0 < Real.sin (δ n)) (hcos : ∀ n, 0 ≤ Real.cos (δ n))
    (ht : MovingSofaOptimality.sigmaAt K (t + Real.pi / 2) = 0) :
    Tendsto (fun n => AngularGrid.firstCornerSecant (U n) (angle n) (δ n)) atTop
      (𝓝 (firstCornerVelocity K t)) := by
  have hnormal : Tendsto (fun n => unitNormal (angle n)) atTop (𝓝 (unitNormal t)) :=
    (Real.continuous_cos.tendsto t |>.comp hangle).prodMk_nhds
      (Real.continuous_sin.tendsto t |>.comp hangle)
  have hsupp : Tendsto (fun n => MovingSofaOptimality.supp (U n) (angle n)) atTop
      (𝓝 (MovingSofaOptimality.supp K t)) := h.support_tendsto_moving hU hK hnormal
  have hsec := h.forwardAngularSecant_tendsto hU hK hB hbox
    (hangle.add_const (Real.pi / 2)) hδ hsin hcos ht
  simpa only [AngularGrid.firstCornerSecant_eq_forward, firstCornerVelocity] using
    (hsupp.add hsec).sub_const 1

theorem CapHausdorffTendsto.secondCornerSecant_tendsto
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
    {angle δ : ℕ → ℝ} {t : ℝ} (hangle : Tendsto angle atTop (𝓝 t))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hsin : ∀ n, 0 < Real.sin (δ n)) (hcos : ∀ n, 0 ≤ Real.cos (δ n))
    (ht : MovingSofaOptimality.sigmaAt K t = 0) :
    Tendsto (fun n => AngularGrid.secondCornerSecant (U n) (angle n) (δ n)) atTop
      (𝓝 (secondCornerVelocity K t)) := by
  have hshift := hangle.add_const (Real.pi / 2)
  have hnormal : Tendsto (fun n => unitNormal (angle n + Real.pi / 2)) atTop
      (𝓝 (unitNormal (t + Real.pi / 2))) :=
    (Real.continuous_cos.tendsto _ |>.comp hshift).prodMk_nhds
      (Real.continuous_sin.tendsto _ |>.comp hshift)
  have hsupp : Tendsto (fun n => MovingSofaOptimality.supp (U n) (angle n + Real.pi / 2)) atTop
      (𝓝 (MovingSofaOptimality.supp K (t + Real.pi / 2))) :=
    h.support_tendsto_moving hU hK hnormal
  have hsec := h.backwardAngularSecant_tendsto hU hK hB hbox hangle hδ hsin hcos ht
  simpa only [AngularGrid.secondCornerSecant_eq_backward, secondCornerVelocity] using
    (hsupp.sub hsec).sub_const 1

namespace AngularGrid

/-- The sampled source may change at every stage. Its moving full normal
is the only angular convergence hypothesis. -/
theorem cornerSecant_tendsto
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
    {level : ℕ → ℕ} (hlevel : Tendsto level atTop atTop)
    (j : ∀ n, SourceIndex (dyadic (level n))) {t : ℝ}
    (hangle : Tendsto (fun n => fullAngle (dyadic (level n)) (j n)) atTop (𝓝 t))
    (htop : t ≠ Real.pi / 2)
    (ht : MovingSofaOptimality.sigmaAt K (companionSourceAngle t) = 0) :
    Tendsto (fun n => cornerSecant (U n) (level n) (j n)) atTop
      (𝓝 (upperCornerVelocity K t)) := by
  have hmesh := mesh_tendsto.comp hlevel
  by_cases hleft : t < Real.pi / 2
  · have hsec := h.firstCornerSecant_tendsto hU hK hB hbox hangle hmesh
      (fun n => mesh_sin_pos (level n)) (fun n => (mesh_cos_pos (level n)).le)
      (by simpa only [companionSourceAngle, if_pos hleft] using ht)
    have heq : ∀ᶠ n in atTop, cornerSecant (U n) (level n) (j n) =
        firstCornerSecant (U n) (fullAngle (dyadic (level n)) (j n)) (mesh (level n)) := by
      filter_upwards [hangle.eventually (isOpen_Iio.mem_nhds hleft)] with n hn
      cases hj : j n with
      | inl s => simp only [cornerSecant, fullAngle]
      | inr s =>
        have hs := interiorPoint_mem (dyadic (level n)) s
        have hbad : (s.val : ℝ) + Real.pi / 2 < Real.pi / 2 := by
          simpa only [hj, fullAngle] using hn
        exact False.elim (by linarith [hs.1])
    simpa only [upperCornerVelocity, if_pos hleft] using
      hsec.congr' (heq.mono fun _ hn => hn.symm)
  · have hright : Real.pi / 2 < t := lt_of_le_of_ne (le_of_not_gt hleft) htop.symm
    have hsec := h.secondCornerSecant_tendsto hU hK hB hbox
      (hangle.sub_const (Real.pi / 2)) hmesh
      (fun n => mesh_sin_pos (level n)) (fun n => (mesh_cos_pos (level n)).le)
      (by simpa only [companionSourceAngle, if_neg hleft] using ht)
    have heq : ∀ᶠ n in atTop, cornerSecant (U n) (level n) (j n) =
        secondCornerSecant (U n) (fullAngle (dyadic (level n)) (j n) - Real.pi / 2)
          (mesh (level n)) := by
      filter_upwards [hangle.eventually (isOpen_Ioi.mem_nhds hright)] with n hn
      cases hj : j n with
      | inl s =>
        have hs := interiorPoint_mem (dyadic (level n)) s
        have hbad : Real.pi / 2 < (s.val : ℝ) := by
          simpa only [hj, fullAngle] using hn
        exact False.elim (by linarith [hs.2])
      | inr s => simp only [cornerSecant, fullAngle, add_sub_cancel_right]
    simpa only [upperCornerVelocity, if_neg hleft] using
      hsec.congr' (heq.mono fun _ hn => hn.symm)

theorem sampledCurvatureDensity_tendsto
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
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

end AngularGrid

end AmbidextrousSofa
