module

public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Function.JacobianOneDim

@[expose] public section

/-!
# Saturation along a monotone graph, including constant pieces

If every measurable parameter set carries exactly the length of its
image under a monotone coordinate, its density is the coordinate
derivative almost everywhere. The coordinate may have constant pieces.
A measurable set where the stated derivative exists is retained in
each area-formula application, and its null complement is removed only
from the parameter measure.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem ae_weight_eq_deriv_of_monotone_image_mass
    {S : Set ℝ} {X XD w : ℝ → ℝ}
    (hS : MeasurableSet S) (hmono : MonotoneOn X S)
    (hw : Measurable w) (hXD : Measurable XD)
    (hw0 : ∀ᵐ t ∂volume.restrict S, 0 ≤ w t)
    (hXD0 : ∀ᵐ t ∂volume.restrict S, 0 ≤ XD t)
    (hD : ∀ᵐ t ∂volume.restrict S, HasDerivAt X (XD t) t)
    (hmass : ∀ T : Set ℝ, MeasurableSet T → T ⊆ S →
      (∫⁻ t in T, ENNReal.ofReal (w t)) = volume (X '' T)) :
    ∀ᵐ t ∂volume.restrict S, w t = XD t := by
  obtain ⟨D, hDS, hDm, hDX⟩ := hD.exists_measurable_mem
  have heq : (fun t => ENNReal.ofReal (w t)) =ᵐ[volume.restrict S]
      fun t => ENNReal.ofReal (XD t) := by
    rw [← Measure.restrict_eq_self_of_ae_mem hDS, Measure.restrict_restrict hDm]
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hw.ennreal_ofReal
      hXD.ennreal_ofReal fun A hA _ => ?_
    have hT := hA.inter (hDm.inter hS)
    have hTS : A ∩ (D ∩ S) ⊆ S := inter_subset_right.trans inter_subset_right
    rw [Measure.restrict_restrict hA, hmass _ hT hTS, lintegral_deriv_eq_volume_image_of_monotoneOn
      hT (fun t ht => (hDX t ht.2.1).hasDerivWithinAt) (hmono.mono hTS)]
  filter_upwards [heq, hw0, hXD0] with t ht ht0 hd0
  exact (ENNReal.ofReal_eq_ofReal_iff ht0 hd0).1 ht

end AmbidextrousSofa
