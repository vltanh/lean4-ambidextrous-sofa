module

public import AmbidextrousSofa.Analysis.FiniteNicheOscillation
public import AmbidextrousSofa.Analysis.EndpointPositivity

@[expose] public section

/-!
# The central niche-height bound for every canonical full maximum

The finite erosion sum controls the total variation of the physical
polygon niche. Concavity controls the two exterior roof variations even
when a selected polygon's highest point moves between the wings. The
actual axis-height limits and the vanishing erosion moments pass this
pointwise estimate to any prescribed full maximizer. Endpoint stationarity
then gives the central bound by half the sum of the two axis heights.

This argument does not require an identification of weak occupation
measures, a smooth roof, a unique active wall, or a prescribed floor set.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AmbidextrousSofa

theorem IsFullCapMaximizer.middle_roof_sum_eq_two_sub_abs_of_affine
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    capRoof U (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) +
      capRoof U (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) =
      2 - |capRoof U (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) -
        capRoof U (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)| := by
  obtain ⟨m, c, haffine⟩ := haffine
  have h1 := capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip
  rcases le_total 0 m with hm | hm
  · rw [hU.middle_right_eq_one_of_affine_nonneg hheight hm haffine,
      abs_of_nonneg (sub_nonneg.2 (h1 _))]
    ring
  · rw [hU.middle_left_eq_one_of_affine_nonpos hheight hm haffine,
      abs_of_nonpos (sub_nonpos.2 (h1 _))]
    ring

open AngularGrid FinitePolygon in
/-- The central height estimate is a consequence of actual maximality.
The selected approximations and their vanishing moments are constructed
inside the proof; none is an additional assumption of this theorem. -/
theorem IsFullCapMaximizer.sweptNiche_le_half_endpoint_height_sum_of_affine
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      sweptNiche U (Real.pi / 2) x ≤
        (capRoof U (horizontalRight U) + capRoof U (horizontalLeft U)) / 2 := by
  intro x hx
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  have hbox : U ⊆ Icc (horizontalLeft U - 1) (horizontalRight U + 1) ×ˢ Icc (0 : ℝ) 1 :=
    fun p hp => ⟨⟨by linarith [(hU.isCap.fst_mem_Icc hp).1],
      by linarith [(hU.isCap.fst_mem_Icc hp).2]⟩, hU.isCap.inStrip hp⟩
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, -, hHausdorff⟩ :=
    exists_selected_sequence hU (by linarith) hbox
  replace hlevel := tendsto_atTop_mono hlevel tendsto_id
  replace hc := fun n => (hc n).le
  have hcap : ∀ n, IsDownwardCap (V n) := fun n => (hV n).isCap
  have hW : 1 < capWidth U := one_lt_M.trans_le hU.width_bounds.1
  have hlr' : horizontalLeft U < horizontalRight U := sub_pos.1 (zero_lt_one.trans hW)
  -- The finite niche oscillation along the selected polygons, at the point `t n` of the middle
  -- interval of `V n` with the relative position of `x`.
  let u := horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4
  let v := horizontalRight U - (horizontalRight U - horizontalLeft U) / 4
  let un : ℕ → ℝ := fun n => horizontalLeft (V n) +
    (horizontalRight (V n) - horizontalLeft (V n)) / 4
  let vn : ℕ → ℝ := fun n => horizontalRight (V n) -
    (horizontalRight (V n) - horizontalLeft (V n)) / 4
  have huv : u < v := by dsimp only [u, v]; linarith
  have hx' : x ∈ Icc u v := hx
  let w : ℝ := (x - u) / (v - u)
  have hw : w ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg (sub_nonneg.2 hx'.1) (sub_pos.2 huv).le,
    (div_le_one (sub_pos.2 huv)).2 (by linarith [hx'.2])⟩
  have hxid : u + w * (v - u) = x := by
    dsimp only [w]
    rw [div_mul_cancel₀ _ (sub_pos.2 huv).ne']
    ring
  let t : ℕ → ℝ := fun n => un n + w * (vn n - un n)
  have huvN (n : ℕ) : un n ≤ vn n := by
    have h := horizontalLeft_le_horizontalRight (hcap n).nonempty (hcap n).isCompact
    dsimp only [un, vn]
    linarith
  have htJ (n : ℕ) : t n ∈ Icc (un n) (vn n) :=
    (convex_Icc _ _).add_smul_sub_mem (left_mem_Icc.2 (huvN n)) (right_mem_Icc.2 (huvN n)) hw
  have hmid (n : ℕ) : Icc (un n) (vn n) ⊆ Icc (horizontalLeft U - 1) (horizontalRight U + 1) :=
    (middleHalfInterval_subset (horizontalLeft_le_horizontalRight (hcap n).nonempty
      (hcap n).isCompact)).trans ((hcap n).projection_subset_Icc_of_box (hV n).inBox)
  have hln := hHausdorff.horizontalLeft_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hU.isCap.isCompact hU.isCap.nonempty
  have hrn := hHausdorff.horizontalRight_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hU.isCap.isCompact hU.isCap.nonempty
  have hun : Tendsto un atTop (𝓝 u) := hln.add ((hrn.sub hln).div_const 4)
  have hvn : Tendsto vn atTop (𝓝 v) := hrn.sub ((hrn.sub hln).div_const 4)
  have hN {s : ℕ → ℝ} {y : ℝ} (hs : ∀ n, s n ∈ Icc (un n) (vn n))
      (hy : Tendsto s atTop (𝓝 y)) := finiteBarrier_dyadic_tendsto hHausdorff hcap hU.isCap
    hlevel (fun n => (hV n).inBox) (fun n => hmid n (hs n)) hy
  have ht : Tendsto t atTop (𝓝 x) := by
    simpa only [hxid] using hun.add ((hvn.sub hun).const_mul w)
  have hniche := (((hN htJ ht).const_mul 2).sub (hN (fun n => left_mem_Icc.2 (huvN n)) hun)).sub
    (hN (fun n => right_mem_Icc.2 (huvN n)) hvn)
  have hroof := (tendsto_const_nhds (x := (2 : ℝ))).sub ((hHausdorff.middleRight_roof_tendsto
    hcap hU.isCap hlr').sub (hHausdorff.middleLeft_roof_tendsto hcap hU.isCap hlr')).abs
  have heL := selected_left_height_tendsto_actual hU.isCap hbox hV hHausdorff hlevel hc hrate hW
    (by linarith)
  have heR := selected_right_height_tendsto_actual hU.isCap hbox hV hHausdorff hlevel hc hrate hW
    (by linarith)
  have hD := erosionMoments_tendsto_zero_of_canonical_maximum hU hheight haffine hbox hV
    hHausdorff hlevel hc hrate (by linarith) (by linarith)
  have hbound := le_of_tendsto_of_tendsto hniche ((((hroof.sub heL).sub heR).add hD.1).add hD.2)
    (by
      filter_upwards [(hHausdorff.capWidth_tendsto hcap hU.isCap).eventually
        (Ioi_mem_nhds (by linarith : 0 < capWidth U))] with n hn
      exact finiteBarrier_peak_le_end_heights_and_moments (hcap n) _ (normal_snd_pos _)
        (wallSlopes_injective _) (hV n).polygon_eq _ none hn (htJ n))
  linarith [hU.middle_roof_sum_eq_two_sub_abs_of_affine hheight haffine,
    hU.endpoint_height_sum_of_affine hheight haffine]

end AmbidextrousSofa
