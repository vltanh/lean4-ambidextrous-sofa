module

public import AmbidextrousSofa.Analysis.RoofContinuity

@[expose] public section

/-!
# Exact differentiation of finite wall envelopes

A finite polygon roof is a minimum of affine lines. A finite physical
niche is a maximum of two-line minima and the zero line. `WallExpr` records
these literal min/max expressions. Distinct line slopes imply that ties
between different sources occur only at finitely many abscissae. Away from
those ties the selected source is locally constant under a support-height
perturbation. A uniform parameter Lipschitz bound justifies differentiating
the ordinary spatial integral.

The resulting derivative is the integral of the selected source's actual
height velocity. In particular a single moved wall contributes its height
velocity times its exposed horizontal length. No differentiability of a
maximum at a tie or convergence of polygonal arclength is assumed.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal NNReal
open scoped Topology

namespace AmbidextrousSofa

/-- A literal finite expression of wall heights. Repeated leaves are allowed. -/
inductive WallExpr (ι : Type*) where
  | leaf (i : ι)
  | minimum (left right : WallExpr ι)
  | maximum (left right : WallExpr ι)

namespace WallExpr

variable {ι : Type*}

def eval : WallExpr ι → (ι → ℝ) → ℝ
  | leaf i, v => v i
  | minimum e f, v => min (eval e v) (eval f v)
  | maximum e f, v => max (eval e v) (eval f v)

/-- A selected attaining leaf; ties consistently select the left minimum
and the right maximum. The integral result is independent of these ties. -/
def source : WallExpr ι → (ι → ℝ) → ι
  | leaf i, _ => i
  | minimum e f, v => if eval e v ≤ eval f v then source e v else source f v
  | maximum e f, v => if eval e v ≤ eval f v then source f v else source e v

theorem eval_eq_source (e : WallExpr ι) (v : ι → ℝ) : e.eval v = v (e.source v) := by
  induction e with
  | leaf i => rfl
  | minimum e f he hf =>
    simp only [eval, source]
    split_ifs with h
    · exact (min_eq_left h).trans he
    · exact (min_eq_right (le_of_not_ge h)).trans hf
  | maximum e f he hf =>
    simp only [eval, source]
    split_ifs with h
    · exact (max_eq_right h).trans hf
    · exact (max_eq_left (le_of_not_ge h)).trans he

theorem continuous_eval (e : WallExpr ι) {α : Type*} [TopologicalSpace α] {v : α → ι → ℝ}
    (hv : ∀ i, Continuous (fun x => v x i)) : Continuous (fun x => e.eval (v x)) := by
  induction e with
  | leaf i => exact hv i
  | minimum e f he hf => exact he.min hf
  | maximum e f he hf => exact he.max hf

theorem lipschitz_eval (e : WallExpr ι) {v : ℝ → ι → ℝ} {K : ℝ≥0}
    (hv : ∀ i, LipschitzWith K (fun x => v x i)) :
    LipschitzWith K (fun x => e.eval (v x)) := by
  induction e with
  | leaf i => exact hv i
  | minimum e f he hf => simpa only [max_self, eval] using he.min hf
  | maximum e f he hf => simpa only [max_self, eval] using he.max hf

theorem measurable_sourceWeight (e : WallExpr ι) {v : ℝ → ι → ℝ}
    (hv : ∀ i, Continuous (fun x => v x i)) (w : ι → ℝ) :
    Measurable (fun x => w (e.source (v x))) := by
  induction e with
  | leaf i =>
    change Measurable (fun _ => w i)
    exact measurable_const
  | minimum e f he hf =>
    change Measurable (fun x => w (if e.eval (v x) ≤ f.eval (v x)
      then e.source (v x) else f.source (v x)))
    simp only [apply_ite]
    exact Measurable.ite
      (measurableSet_le (e.continuous_eval hv).measurable (f.continuous_eval hv).measurable) he hf
  | maximum e f he hf =>
    change Measurable (fun x => w (if e.eval (v x) ≤ f.eval (v x)
      then f.source (v x) else e.source (v x)))
    simp only [apply_ite]
    exact Measurable.ite
      (measurableSet_le (e.continuous_eval hv).measurable (f.continuous_eval hv).measurable) hf he

/-- When different source values are distinct, the whole expression agrees
locally with its selected source, even if that leaf occurs repeatedly. -/
theorem eventuallyEq_source (e : WallExpr ι) {v : ℝ → ι → ℝ}
    (hv : ∀ i, ContinuousAt (fun ε => v ε i) 0) (hinj : Function.Injective (v 0)) :
    (fun ε => e.eval (v ε)) =ᶠ[𝓝 0] (fun ε => v ε (e.source (v 0))) := by
  induction e with
  | leaf i => exact Eventually.of_forall (fun _ => rfl)
  | minimum e f he hf =>
    rcases lt_trichotomy (e.eval (v 0)) (f.eval (v 0)) with hlt | heq | hgt
    · have hvalues : v 0 (e.source (v 0)) < v 0 (f.source (v 0)) := by
        simpa only [← eval_eq_source] using hlt
      simp only [source, if_pos hlt.le]
      filter_upwards [he, hf, (hv _).eventually_lt (hv _) hvalues] with ε heε hfε hε
      simp only [eval, heε, hfε, min_eq_left hε.le]
    · have hsources : e.source (v 0) = f.source (v 0) := by
        apply hinj
        simpa only [← eval_eq_source] using heq
      simp only [source, if_pos heq.le]
      filter_upwards [he, hf] with ε heε hfε
      simp only [eval, heε, hfε, hsources, min_self]
    · have hvalues : v 0 (f.source (v 0)) < v 0 (e.source (v 0)) := by
        simpa only [← eval_eq_source] using hgt
      simp only [source, if_neg (not_le.mpr hgt)]
      filter_upwards [he, hf, (hv _).eventually_lt (hv _) hvalues] with ε heε hfε hε
      simp only [eval, heε, hfε, min_eq_right hε.le]
  | maximum e f he hf =>
    rcases lt_trichotomy (e.eval (v 0)) (f.eval (v 0)) with hlt | heq | hgt
    · have hvalues : v 0 (e.source (v 0)) < v 0 (f.source (v 0)) := by
        simpa only [← eval_eq_source] using hlt
      simp only [source, if_pos hlt.le]
      filter_upwards [he, hf, (hv _).eventually_lt (hv _) hvalues] with ε heε hfε hε
      simp only [eval, heε, hfε, max_eq_right hε.le]
    · have hsources : e.source (v 0) = f.source (v 0) := by
        apply hinj
        simpa only [← eval_eq_source] using heq
      simp only [source, if_pos heq.le]
      filter_upwards [he, hf] with ε heε hfε
      simp only [eval, heε, hfε, hsources, max_self]
    · have hvalues : v 0 (f.source (v 0)) < v 0 (e.source (v 0)) := by
        simpa only [← eval_eq_source] using hgt
      simp only [source, if_neg (not_le.mpr hgt)]
      filter_upwards [he, hf, (hv _).eventually_lt (hv _) hvalues] with ε heε hfε hε
      simp only [eval, heε, hfε, max_eq_left hε.le]

/-- The finite envelope of affine lines under affine support perturbation. -/
def affineEnvelope (e : WallExpr ι) (a b w : ι → ℝ) (ε x : ℝ) : ℝ :=
  e.eval (fun i => a i * x + b i + ε * w i)

def sourceDensity (e : WallExpr ι) (a b w : ι → ℝ) (x : ℝ) : ℝ :=
  w (e.source (fun i => a i * x + b i))

theorem continuous_affineEnvelope (e : WallExpr ι) (a b w : ι → ℝ) (ε : ℝ) :
    Continuous (e.affineEnvelope a b w ε) :=
  e.continuous_eval (fun _ => by fun_prop)

theorem measurable_sourceDensity (e : WallExpr ι) (a b w : ι → ℝ) :
    Measurable (e.sourceDensity a b w) :=
  e.measurable_sourceWeight (fun _ => by fun_prop) w

theorem hasDerivAt_affineEnvelope (e : WallExpr ι) (a b w : ι → ℝ) (x : ℝ)
    (hinj : Function.Injective (fun i => a i * x + b i)) :
    HasDerivAt (fun ε => e.affineEnvelope a b w ε x) (e.sourceDensity a b w x) 0 := by
  have hderiv : HasDerivAt
      (fun ε : ℝ => a (e.source (fun i => a i * x + b i)) * x +
        b (e.source (fun i => a i * x + b i)) +
        ε * w (e.source (fun i => a i * x + b i)))
      (e.sourceDensity a b w x) 0 := by
    simpa only [sourceDensity, zero_add, one_mul, Pi.add_def, id_eq] using
      (hasDerivAt_const (0 : ℝ) (a (e.source (fun i => a i * x + b i)) * x +
        b (e.source (fun i => a i * x + b i)))).add
        ((hasDerivAt_id (0 : ℝ)).mul_const (w (e.source (fun i => a i * x + b i))))
  apply hderiv.congr_of_eventuallyEq
  have h := e.eventuallyEq_source
    (v := fun ε i => a i * x + b i + ε * w i) (fun _ => by fun_prop)
    (by simpa only [zero_mul, add_zero] using hinj)
  simpa only [affineEnvelope, zero_mul, add_zero] using h

/-- Two distinct-slope lines coincide at only one abscissa. The finite
family therefore has distinct values at almost every spatial point. -/
theorem ae_injective_affine [Fintype ι] {a b : ι → ℝ} (ha : Function.Injective a) :
    ∀ᵐ x : ℝ, Function.Injective (fun i => a i * x + b i) := by
  have hpair : ∀ i j : ι, ∀ᵐ x : ℝ, a i * x + b i = a j * x + b j → i = j := by
    intro i j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ _ => hij)
    · have hden : a i - a j ≠ 0 := sub_ne_zero.mpr (fun h => hij (ha h))
      filter_upwards [volume.ae_ne ((b j - b i) / (a i - a j))] with x hx
      intro heq
      exfalso
      apply hx
      apply (eq_div_iff hden).mpr
      nlinarith
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hpair i))] with x hx
  exact fun i j hij => hx i j hij

theorem lipschitz_affineEnvelope_parameter (e : WallExpr ι) (a b w : ι → ℝ)
    {K : ℝ} (hK : 0 ≤ K) (hw : ∀ i, |w i| ≤ K) (x : ℝ) :
    LipschitzWith (Real.nnabs K) (fun ε => e.affineEnvelope a b w ε x) := by
  apply e.lipschitz_eval
  intro i
  apply LipschitzWith.of_dist_le_mul
  intro ε η
  simp only [Real.dist_eq, Real.coe_nnabs, abs_of_nonneg hK]
  calc
    |a i * x + b i + ε * w i - (a i * x + b i + η * w i)| =
        |w i| * |ε - η| := by
      rw [show a i * x + b i + ε * w i - (a i * x + b i + η * w i) =
        w i * (ε - η) by ring, abs_mul]
    _ ≤ K * |ε - η| := mul_le_mul_of_nonneg_right (hw i) (abs_nonneg _)

/-- Exact derivative of the ordinary integral of a finite envelope. Every
hypothesis is about the displayed finite line data, not an asserted
exposure formula or a maximizer. -/
theorem hasDerivAt_integral_affineEnvelope [Fintype ι] (e : WallExpr ι)
    (a b w : ι → ℝ) (ha : Function.Injective a) (l r : ℝ) :
    HasDerivAt (fun ε => ∫ x in l..r, e.affineEnvelope a b w ε x)
      (∫ x in l..r, e.sourceDensity a b w x) 0 := by
  let K : ℝ := ∑ i, |w i|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun i _ => abs_nonneg (w i))
  have hw : ∀ i, |w i| ≤ K := fun i =>
    Finset.single_le_sum (fun j _ => abs_nonneg (w j)) (Finset.mem_univ i)
  have hdiff : ∀ᵐ x : ℝ, HasDerivAt (fun ε => e.affineEnvelope a b w ε x)
      (e.sourceDensity a b w x) 0 := by
    filter_upwards [ae_injective_affine (b := b) ha] with x hx
    exact e.hasDerivAt_affineEnvelope a b w x hx
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
    (s := univ) (bound := fun _ : ℝ => K) (by simp)
    (Eventually.of_forall (fun ε =>
      (e.continuous_affineEnvelope a b w ε).measurable.aestronglyMeasurable))
    ((e.continuous_affineEnvelope a b w 0).intervalIntegrable l r)
    (e.measurable_sourceDensity a b w).aestronglyMeasurable
    (Eventually.of_forall (fun x _ =>
      (e.lipschitz_affineEnvelope_parameter a b w hK hw x).lipschitzOnWith))
    intervalIntegrable_const (hdiff.mono (fun _ h _ => h))).2

/-- The actual spatial set on which a particular leaf supplies the envelope. -/
def sourceSet (e : WallExpr ι) (a b : ι → ℝ) (j : ι) : Set ℝ :=
  {x | e.source (fun i => a i * x + b i) = j}

theorem measurableSet_sourceSet [DecidableEq ι] (e : WallExpr ι) (a b : ι → ℝ) (j : ι) :
    MeasurableSet (e.sourceSet a b j) := by
  have heq : e.sourceSet a b j =
      (e.sourceDensity a b (fun i => if i = j then 1 else 0)) ⁻¹' {(1 : ℝ)} := by
    ext x
    simp only [sourceSet, sourceDensity, mem_setOf_eq, mem_preimage, mem_singleton_iff]
    split_ifs <;> simp_all
  rw [heq]
  exact (e.measurable_sourceDensity a b _ ) (measurableSet_singleton 1)

theorem sourceDensity_single [DecidableEq ι] (e : WallExpr ι)
    (a b : ι → ℝ) (j : ι) (k : ℝ) :
    e.sourceDensity a b (fun i => if i = j then k else 0) =
      (e.sourceSet a b j).indicator (fun _ => k) := by
  funext x
  by_cases hx : e.source (fun i => a i * x + b i) = j
  · simp [sourceDensity, sourceSet, hx]
  · simp [sourceDensity, sourceSet, hx]

/-- A one-wall height variation differentiates to the actual exposed
horizontal length times its height velocity. -/
theorem hasDerivAt_integral_single_wall [Fintype ι] [DecidableEq ι]
    (e : WallExpr ι) (a b : ι → ℝ) (ha : Function.Injective a)
    (j : ι) (k : ℝ) {l r : ℝ} (hlr : l ≤ r) :
    HasDerivAt (fun ε => ∫ x in l..r,
      e.affineEnvelope a b (fun i => if i = j then k else 0) ε x)
      ((volume.real (Ioc l r ∩ e.sourceSet a b j)) * k) 0 := by
  have h := e.hasDerivAt_integral_affineEnvelope a b
    (fun i => if i = j then k else 0) ha l r
  rw [e.sourceDensity_single a b j k, intervalIntegral.integral_of_le hlr,
    setIntegral_indicator (e.measurableSet_sourceSet a b j), setIntegral_const,
    smul_eq_mul] at h
  exact h

end WallExpr

end AmbidextrousSofa
