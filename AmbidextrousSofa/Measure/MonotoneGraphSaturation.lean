import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Saturation along a monotone graph, including constant pieces

If every measurable parameter set carries exactly the length of its
image under a monotone coordinate, its density is the coordinate
derivative almost everywhere. The coordinate may have constant pieces.
The measurable set where the stated derivative exists is retained in
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
  let D : Set ℝ := {t | DifferentiableAt ℝ X t ∧ deriv X t = XD t}
  have hDm : MeasurableSet D :=
    (measurableSet_of_differentiableAt ℝ X).inter
      (measurableSet_eq_fun (measurable_deriv X) hXD)
  have hDa : ∀ᵐ t ∂volume.restrict S, t ∈ D :=
    hD.mono (fun _ ht => ⟨ht.differentiableAt, ht.deriv⟩)
  have hsame : S ∩ D =ᵐ[volume] S := by
    filter_upwards [(ae_restrict_iff' hS).mp hDa] with t ht
    exact propext ⟨fun h => h.1, fun h => ⟨h, ht h⟩⟩
  have hrestrict : volume.restrict (S ∩ D) = volume.restrict S :=
    Measure.restrict_congr_set hsame
  have heq : (fun t => ENNReal.ofReal (w t)) =ᵐ[volume.restrict (S ∩ D)]
      (fun t => ENNReal.ofReal (XD t)) := by
    apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
      hw.ennreal_ofReal hXD.ennreal_ofReal
    intro A hA _
    rw [Measure.restrict_restrict hA]
    have hT : MeasurableSet (A ∩ (S ∩ D)) := hA.inter (hS.inter hDm)
    have hTS : A ∩ (S ∩ D) ⊆ S := inter_subset_right.trans inter_subset_left
    calc
      (∫⁻ t in A ∩ (S ∩ D), ENNReal.ofReal (w t)) =
          volume (X '' (A ∩ (S ∩ D))) := hmass _ hT hTS
      _ = ∫⁻ t in A ∩ (S ∩ D), ENNReal.ofReal (XD t) := by
        symm
        apply lintegral_deriv_eq_volume_image_of_monotoneOn hT _ (hmono.mono hTS)
        intro t ht
        have hd : DifferentiableAt ℝ X t ∧ deriv X t = XD t := ht.2.2
        have hd' : HasDerivAt X (XD t) t := by
          rw [← hd.2]
          exact hd.1.hasDerivAt
        exact hd'.hasDerivWithinAt
  rw [hrestrict] at heq
  filter_upwards [heq, hw0, hXD0] with t ht ht0 hd0
  simpa only [ENNReal.toReal_ofReal ht0, ENNReal.toReal_ofReal hd0] using
    congrArg ENNReal.toReal ht

end AmbidextrousSofa
