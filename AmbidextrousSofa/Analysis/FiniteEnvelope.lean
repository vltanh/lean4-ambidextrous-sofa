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
  | minimum e f he hf => simp only [eval, source, min_def, apply_ite v, he, hf]
  | maximum e f he hf => simp only [eval, source, max_def, apply_ite v, he, hf]

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

/-- When different source values are distinct, the whole expression agrees
locally with its selected source, even if that leaf occurs repeatedly. -/
theorem eventuallyEq_source (e : WallExpr ι) {v : ℝ → ι → ℝ}
    (hv : ∀ i, ContinuousAt (fun ε => v ε i) 0) (hinj : Function.Injective (v 0)) :
    (fun ε => e.eval (v ε)) =ᶠ[𝓝 0] (fun ε => v ε (e.source (v 0))) := by
  suffices ∀ᶠ ε in 𝓝 0, e.source (v ε) = e.source (v 0) from
    this.mono fun ε hε => by simp only [eval_eq_source, hε]
  induction e with
  | leaf i => exact Eventually.of_forall fun _ => rfl
  | minimum e f he hf | maximum e f he hf =>
    simp only [source, eval_eq_source]
    rcases lt_trichotomy (v 0 (e.source (v 0))) (v 0 (f.source (v 0))) with h | h | h
    · filter_upwards [he, hf, (hv _).eventually_lt (hv _) h] with ε h1 h2 h3
      simp [h1, h2, h3.le, h.le]
    · filter_upwards [he, hf] with ε h1 h2
      simp [h1, h2, hinj h]
    · filter_upwards [he, hf, (hv _).eventually_lt (hv _) h] with ε h1 h2 h3
      simp [h1, h2, not_le.mpr h3, not_le.mpr h]

/-- The finite envelope of affine lines under affine support perturbation. -/
def affineEnvelope (e : WallExpr ι) (a b w : ι → ℝ) (ε x : ℝ) : ℝ :=
  e.eval (fun i => a i * x + b i + ε * w i)

def sourceDensity (e : WallExpr ι) (a b w : ι → ℝ) (x : ℝ) : ℝ :=
  w (e.source (fun i => a i * x + b i))

theorem continuous_affineEnvelope (e : WallExpr ι) (a b w : ι → ℝ) (ε : ℝ) :
    Continuous (e.affineEnvelope a b w ε) :=
  e.continuous_eval (fun _ => by fun_prop)

theorem measurable_sourceDensity (e : WallExpr ι) (a b w : ι → ℝ) :
    Measurable (e.sourceDensity a b w) := by
  have hv : ∀ i, Continuous (fun x : ℝ => a i * x + b i) := fun _ => by fun_prop
  unfold sourceDensity
  induction e with
  | leaf i => simp only [source, measurable_const]
  | minimum e f he hf | maximum e f he hf =>
    simp only [source, apply_ite]
    exact Measurable.ite (measurableSet_le (e.continuous_eval hv).measurable
      (f.continuous_eval hv).measurable) (by assumption) (by assumption)

theorem hasDerivAt_affineEnvelope (e : WallExpr ι) (a b w : ι → ℝ) (x : ℝ)
    (hinj : Function.Injective (fun i => a i * x + b i)) :
    HasDerivAt (fun ε => e.affineEnvelope a b w ε x) (e.sourceDensity a b w x) 0 := by
  have h := e.eventuallyEq_source (v := fun ε i => a i * x + b i + ε * w i)
    (fun _ => by fun_prop) (by simpa only [zero_mul, add_zero] using hinj)
  simp only [zero_mul, add_zero] at h
  exact ((((hasDerivAt_id' (0 : ℝ)).mul_const _).const_add _).congr_of_eventuallyEq h).congr_deriv
    (one_mul _)

/-- Two distinct-slope lines coincide at only one abscissa. The finite
family therefore has distinct values at almost every spatial point. -/
theorem ae_injective_affine [Fintype ι] {a b : ι → ℝ} (ha : Function.Injective a) :
    ∀ᵐ x : ℝ, Function.Injective (fun i => a i * x + b i) := by
  have hpair (i j : ι) : ∀ᵐ x : ℝ, a i * x + b i = a j * x + b j → i = j := by
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ _ => hij
    filter_upwards [volume.ae_ne ((b j - b i) / (a i - a j))] with x hx heq
    exact absurd ((eq_div_iff (sub_ne_zero.mpr (ha.ne hij))).mpr (by linarith)) hx
  exact (ae_all_iff.mpr fun i => ae_all_iff.mpr (hpair i)).mono fun _ hx => hx

theorem lipschitz_affineEnvelope_parameter (e : WallExpr ι) (a b w : ι → ℝ)
    {K : ℝ} (hK : 0 ≤ K) (hw : ∀ i, |w i| ≤ K) (x : ℝ) :
    LipschitzWith (Real.nnabs K) (fun ε => e.affineEnvelope a b w ε x) := by
  refine e.lipschitz_eval fun i => LipschitzWith.of_dist_le_mul fun ε η => ?_
  simp only [Real.dist_eq, Real.coe_nnabs, abs_of_nonneg hK]
  rw [show a i * x + b i + ε * w i - (a i * x + b i + η * w i) = w i * (ε - η) by ring, abs_mul]
  exact mul_le_mul_of_nonneg_right (hw i) (abs_nonneg _)

/-- Exact derivative of the ordinary integral of a finite envelope. Every
hypothesis is about the displayed finite line data, not an asserted
exposure formula or a maximizer. -/
theorem hasDerivAt_integral_affineEnvelope [Fintype ι] (e : WallExpr ι)
    (a b w : ι → ℝ) (ha : Function.Injective a) (l r : ℝ) :
    HasDerivAt (fun ε => ∫ x in l..r, e.affineEnvelope a b w ε x)
      (∫ x in l..r, e.sourceDensity a b w x) 0 :=
  (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
    (s := univ) (bound := fun _ : ℝ => ∑ i, |w i|) (by simp)
    (Eventually.of_forall (fun ε =>
      (e.continuous_affineEnvelope a b w ε).measurable.aestronglyMeasurable))
    ((e.continuous_affineEnvelope a b w 0).intervalIntegrable l r)
    (e.measurable_sourceDensity a b w).aestronglyMeasurable
    (Eventually.of_forall (fun x _ => (e.lipschitz_affineEnvelope_parameter a b w
      (Finset.sum_nonneg fun i _ => abs_nonneg (w i))
      (fun i => Finset.single_le_sum (fun j _ => abs_nonneg (w j)) (Finset.mem_univ i))
      x).lipschitzOnWith))
    intervalIntegrable_const ((ae_injective_affine (b := b) ha).mono
      fun x hx _ => e.hasDerivAt_affineEnvelope a b w x hx)).2

/-- The actual spatial set on which a particular leaf supplies the envelope. -/
def sourceSet (e : WallExpr ι) (a b : ι → ℝ) (j : ι) : Set ℝ :=
  {x | e.source (fun i => a i * x + b i) = j}

theorem sourceDensity_single [DecidableEq ι] (e : WallExpr ι)
    (a b : ι → ℝ) (j : ι) (k : ℝ) :
    e.sourceDensity a b (fun i => if i = j then k else 0) =
      (e.sourceSet a b j).indicator (fun _ => k) := by
  funext x
  by_cases hx : e.source (fun i => a i * x + b i) = j <;> simp [sourceDensity, sourceSet, hx]

theorem measurableSet_sourceSet [DecidableEq ι] (e : WallExpr ι) (a b : ι → ℝ) (j : ι) :
    MeasurableSet (e.sourceSet a b j) :=
  (measurable_indicator_const_iff (1 : ℝ)).mp
    (e.sourceDensity_single a b j 1 ▸ e.measurable_sourceDensity a b _)

end WallExpr

end AmbidextrousSofa
