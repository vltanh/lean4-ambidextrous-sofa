module

public import AmbidextrousSofa.Analysis.GridPolygon
public import AmbidextrousSofa.Geometry.UpwardSupport

@[expose] public section

/-!
# The open dyadic sources determine the actual cap

The endpoint directions do not supply moving walls. They are recovered
by continuity from the interior samples. A factor vanishing at the two
endpoints lets the closed-grid density theorem prove this without adding
axis samples to the polygon's moving support array.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

namespace AngularGrid

theorem eqOn_quarter_of_interior_dyadic {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hsample : ∀ n, ∀ t : InteriorPoint (dyadic n), f t.val = g t.val) :
    EqOn f g (Icc (0 : ℝ) (Real.pi / 2)) := by
  classical
  let H : QuarterAngle → ℝ := fun t =>
    (t : ℝ) * (Real.pi / 2 - (t : ℝ)) * (f t - g t)
  have hH : Continuous H := by
    exact (continuous_subtype_val.mul (continuous_const.sub continuous_subtype_val)).mul
      ((hf.comp continuous_subtype_val).sub (hg.comp continuous_subtype_val))
  have hzero : ∀ t, H t = 0 := by
    intro t
    refine dense_iUnion_dyadic.induction (P := fun t => H t = 0) ?_
      (isClosed_eq hH continuous_const) t
    intro s hs
    obtain ⟨n, hn⟩ := mem_iUnion.mp hs
    by_cases hs0 : (s : ℝ) = 0
    · simp [H, hs0]
    by_cases hsL : (s : ℝ) = Real.pi / 2
    · simp [H, hsL]
    · have hsopen : 0 < (s : ℝ) ∧ (s : ℝ) < Real.pi / 2 :=
        ⟨lt_of_le_of_ne s.property.1 (Ne.symm hs0), lt_of_le_of_ne s.property.2 hsL⟩
      let u : InteriorPoint (dyadic n) := ⟨s, Finset.mem_filter.mpr ⟨hn, hsopen⟩⟩
      have hfg : f s = g s := hsample n u
      simp only [H, hfg, sub_self, mul_zero]
  have hopen : Ioo (0 : ℝ) (Real.pi / 2) ⊆ {t | f t = g t} := by
    intro t ht
    have h := hzero ⟨t, ht.1.le, ht.2.le⟩
    change t * (Real.pi / 2 - t) * (f t - g t) = 0 at h
    have hfactor : t * (Real.pi / 2 - t) ≠ 0 :=
      mul_ne_zero ht.1.ne' (sub_pos.mpr ht.2).ne'
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hfactor)
  have hclosed := closure_minimal hopen (isClosed_eq hf hg)
  rw [closure_Ioo (by linarith [Real.pi_pos] : (0 : ℝ) ≠ Real.pi / 2)] at hclosed
  exact hclosed

/-- Equality at every persistent dyadic source determines the whole
compact convex cap, including both vertical end faces. -/
theorem eq_of_dyadic_support_eq {U V : Set Plane}
    (hU : IsDownwardCap U) (hV : IsDownwardCap V)
    (hsupport : ∀ n, ∀ i : SourceIndex (dyadic n),
      support U (normal (dyadic n) i) = support V (normal (dyadic n) i)) : U = V := by
  apply hU.eq_of_quarter_support_eq hV
  · exact eqOn_quarter_of_interior_dyadic
      ((continuous_support hU.isCompact).comp continuous_unitNormal)
      ((continuous_support hV.isCompact).comp continuous_unitNormal)
      (fun n t => hsupport n (Sum.inl t))
  · exact eqOn_quarter_of_interior_dyadic
      ((continuous_support hU.isCompact).comp continuous_companionNormal)
      ((continuous_support hV.isCompact).comp continuous_companionNormal)
      (fun n t => hsupport n (Sum.inr t))

end AngularGrid

end AmbidextrousSofa
