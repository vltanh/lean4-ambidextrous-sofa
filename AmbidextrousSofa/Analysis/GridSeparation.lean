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
  have hzero (t : QuarterAngle) : (t : ℝ) * (Real.pi / 2 - t) * (f t - g t) = 0 := by
    refine dense_iUnion_dyadic.induction (fun s hs => ?_)
      (isClosed_eq (by fun_prop) continuous_const) t
    obtain ⟨n, hn⟩ := mem_iUnion.mp hs
    rcases s.2.1.eq_or_lt with h0 | h0
    · simp [← h0]
    rcases s.2.2.eq_or_lt with h1 | h1
    · simp [h1]
    simp [show f s = g s from hsample n ⟨s, Finset.mem_filter.mpr ⟨hn, h0, h1⟩⟩]
  rw [← closure_Ioo (by positivity : (0 : ℝ) ≠ Real.pi / 2)]
  refine closure_minimal (fun t ht => show f t = g t by
    simpa [ht.1.ne', (sub_pos.2 ht.2).ne', sub_eq_zero] using hzero ⟨t, ht.1.le, ht.2.le⟩)
    (isClosed_eq hf hg)

/-- Equality at every persistent dyadic source determines the whole
compact convex cap, including both vertical end faces. -/
theorem eq_of_dyadic_support_eq {U V : Set Plane}
    (hU : IsDownwardCap U) (hV : IsDownwardCap V)
    (hsupport : ∀ n, ∀ i : SourceIndex (dyadic n),
      support U (normal (dyadic n) i) = support V (normal (dyadic n) i)) : U = V := by
  have hc := continuous_support hU.isCompact
  have hc' := continuous_support hV.isCompact
  exact hU.eq_of_quarter_support_eq hV
    (eqOn_quarter_of_interior_dyadic (hc.comp continuous_unitNormal)
      (hc'.comp continuous_unitNormal) fun n t => hsupport n (.inl t))
    (eqOn_quarter_of_interior_dyadic (hc.comp continuous_companionNormal)
      (hc'.comp continuous_companionNormal) fun n t => hsupport n (.inr t))

end AngularGrid

end AmbidextrousSofa
