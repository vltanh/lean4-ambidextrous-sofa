module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

@[expose] public section

/-!
# Real densities for finite source submeasures

The real representative is taken directly from the Radon--Nikodym
derivative. Finite source measures give integrable representatives; their
absolutely continuous reconstruction, addition, and identification with
a prescribed density are all almost everywhere statements over the
same base measure. The final identity transports a pulled-back weight
through a measurable projection without requiring injectivity.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal NNReal

namespace AmbidextrousSofa

def realRnDensity (μ ν : Measure ℝ) (x : ℝ) : ℝ := (μ.rnDeriv ν x).toReal

theorem measurable_realRnDensity (μ ν : Measure ℝ) : Measurable (realRnDensity μ ν) :=
  (Measure.measurable_rnDeriv μ ν).ennreal_toReal

theorem realRnDensity_nonneg (μ ν : Measure ℝ) (x : ℝ) : 0 ≤ realRnDensity μ ν x :=
  ENNReal.toReal_nonneg

theorem integrable_realRnDensity (μ ν : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (realRnDensity μ ν) ν := by
  have hi := Measure.integrableOn_toReal_rnDeriv
    (μ := μ) (ν := ν) (s := univ) (measure_ne_top _ _)
  simp only [IntegrableOn, Measure.restrict_univ] at hi
  exact hi

theorem withDensity_realRnDensity (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    ν.withDensity (fun x => ENNReal.ofReal (realRnDensity μ ν x)) = μ := by
  calc
    _ = ν.withDensity (μ.rnDeriv ν) := by
      apply withDensity_congr_ae
      filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
      exact ENNReal.ofReal_toReal hx.ne
    _ = μ := Measure.withDensity_rnDeriv_eq μ ν hμν

theorem ae_realRnDensity_add (μ κ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure κ] [SigmaFinite ν] :
    ∀ᵐ x ∂ν, realRnDensity (μ + κ) ν x = realRnDensity μ ν x + realRnDensity κ ν x := by
  filter_upwards [Measure.rnDeriv_add μ κ ν,
    Measure.rnDeriv_lt_top μ ν, Measure.rnDeriv_lt_top κ ν] with x hadd hμ hκ
  change ((μ + κ).rnDeriv ν x).toReal = (μ.rnDeriv ν x).toReal + (κ.rnDeriv ν x).toReal
  rw [hadd, Pi.add_apply, ENNReal.toReal_add hμ.ne hκ.ne]

theorem ae_realRnDensity_eq_of_withDensity₀
    {μ ν : Measure ℝ} [SigmaFinite ν] {ρ : ℝ → ℝ}
    (hρ : AEMeasurable ρ ν) (hρ0 : ∀ᵐ x ∂ν, 0 ≤ ρ x)
    (hμ : μ = ν.withDensity (fun x => ENNReal.ofReal (ρ x))) :
    realRnDensity μ ν =ᵐ[ν] ρ := by
  have h := Measure.rnDeriv_withDensity₀ ν hρ.ennreal_ofReal
  rw [← hμ] at h
  filter_upwards [h, hρ0] with x hx hx0
  change (μ.rnDeriv ν x).toReal = ρ x
  rw [hx, ENNReal.toReal_ofReal hx0]

theorem ae_realRnDensity_eq_of_withDensity
    {μ ν : Measure ℝ} [SigmaFinite ν] {ρ : ℝ → ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hμ : μ = ν.withDensity (fun x => ENNReal.ofReal (ρ x))) :
    realRnDensity μ ν =ᵐ[ν] ρ :=
  ae_realRnDensity_eq_of_withDensity₀ hρ.aemeasurable (ae_of_all _ hρ0) hμ

theorem map_withDensity_comp
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) {f : Ω → Ξ} {w : Ξ → ℝ≥0∞}
    (hf : Measurable f) (hw : Measurable w) :
    (μ.withDensity (fun x => w (f x))).map f = (μ.map f).withDensity w := by
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply hf hE, withDensity_apply _ (hf hE), withDensity_apply _ hE]
  exact (setLIntegral_map hE hw hf).symm

end AmbidextrousSofa
