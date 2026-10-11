module

public import AmbidextrousSofa.Analysis.CapOrder

@[expose] public section

/-!
# Vertical extrusion and height saturation of actual caps

An extrusion raises the whole roof and fills down to the baseline. Its
upward supports gain exactly the vertical translation pairing. Every
interior wall and the actual terminal wall therefore gain the same amount;
the nonnegative barrier gains at most that amount. The exterior and middle
windows have equal length, so the actual scalar score cannot decrease.

The final construction saturates any cap to height one. It applies to the
broad cap domain, including caps initially contained in the baseline.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

/-- Raise the roof by `ε`, retaining every vertical segment down to zero. -/
def verticalExtrusion (U : Set Plane) (ε : ℝ) : Set Plane :=
  upperCap ((fun p : Plane => p + (0, ε)) '' U)

theorem mem_verticalExtrusion_iff (U : Set Plane) (ε : ℝ) (p : Plane) :
    p ∈ verticalExtrusion U ε ↔
      0 ≤ p.2 ∧ ∃ q ∈ U, q.1 = p.1 ∧ p.2 ≤ q.2 + ε := by
  simp only [verticalExtrusion, upperCap, mem_ofPred_eq, mem_image, Prod.ext_iff, Prod.fst_add,
    Prod.snd_add, add_zero]
  exact ⟨fun ⟨hp0, _, hpy, q, hq, hx, hy⟩ => ⟨hp0, q, hq, hx, hy ▸ hpy⟩,
    fun ⟨hp0, q, hq, hx, hpy⟩ => ⟨hp0, _, hpy, q, hq, hx, rfl⟩⟩

theorem IsDownwardCap.subset_verticalExtrusion {U : Set Plane}
    (hU : IsDownwardCap U) {ε : ℝ} (hε : 0 ≤ ε) : U ⊆ verticalExtrusion U ε := fun p hp =>
  (mem_verticalExtrusion_iff U ε p).mpr ⟨(hU.inStrip hp).1, p, hp, rfl, by linarith⟩

theorem IsDownwardCap.verticalLift_nonneg {U : Set Plane}
    (hU : IsDownwardCap U) {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ p ∈ ((fun q : Plane => q + (0, ε)) '' U), 0 ≤ p.2 := fun _ ⟨_, hq, h⟩ =>
  h ▸ add_nonneg (hU.inStrip hq).1 hε

theorem IsDownwardCap.horizontalProjection_verticalExtrusion {U : Set Plane}
    (hU : IsDownwardCap U) {ε : ℝ} (hε : 0 ≤ ε) :
    horizontalProjection (verticalExtrusion U ε) = horizontalProjection U := by
  rw [verticalExtrusion, horizontalProjection_upperCap (hU.verticalLift_nonneg hε),
    horizontalProjection, horizontalProjection, image_image]
  simp

theorem IsDownwardCap.isDownwardCap_verticalExtrusion {U : Set Plane}
    (hU : IsDownwardCap U) {ε : ℝ} (hε : 0 ≤ ε)
    (hheight : ∀ p ∈ U, p.2 + ε ≤ 1) : IsDownwardCap (verticalExtrusion U ε) :=
  isDownwardCap_upperCap (hU.nonempty.image _) (hU.isCompact.image (by fun_prop))
    (by simpa only [add_comm] using hU.convex.translate ((0, ε) : Plane))
    fun _ ⟨q, hq, h⟩ => h ▸ ⟨add_nonneg (hU.inStrip hq).1 hε, hheight q hq⟩

/-- Roof translation holds on the actual common projection. Outside it the
roof convention remains zero, so no global additive formula is asserted. -/
theorem IsDownwardCap.capRoof_verticalExtrusion {U : Set Plane}
    (hU : IsDownwardCap U) {ε : ℝ} (hε : 0 ≤ ε) {x : ℝ}
    (hx : x ∈ horizontalProjection U) :
    capRoof (verticalExtrusion U ε) x = capRoof U x + ε := by
  have hcompact : IsCompact (verticalExtrusion U ε) :=
    isCompact_upperCap (hU.isCompact.image (by fun_prop)) (hU.verticalLift_nonneg hε)
  refine le_antisymm ?_ (le_capRoof hcompact ((mem_verticalExtrusion_iff U ε _).mpr
    ⟨add_nonneg (capRoof_nonneg hU.isCompact (fun p hp => (hU.inStrip hp).1) x) hε, _,
      capRoof_mem hU.isCompact hx, rfl, le_rfl⟩))
  obtain ⟨-, q, hq, hqx, hle⟩ := (mem_verticalExtrusion_iff U ε _).mp
    (capRoof_mem hcompact (hU.horizontalProjection_verticalExtrusion hε ▸ hx))
  dsimp only at hqx hle
  subst hqx
  linarith [le_capRoof hU.isCompact hq]

/-- Every upward support receives the exact vertical translation correction. -/
theorem IsDownwardCap.support_verticalExtrusion {U : Set Plane}
    (hU : IsDownwardCap U) {ε : ℝ} (hε : 0 ≤ ε) {v : Plane} (hv : 0 ≤ v.2) :
    support (verticalExtrusion U ε) v = support U v + ε * v.2 := by
  rw [verticalExtrusion, support_upperCap (hU.isCompact.image (by fun_prop))
    (hU.nonempty.image _) (hU.verticalLift_nonneg hε) hv,
    support_translate hU.isCompact hU.nonempty]
  simp only [coordDot, zero_mul, zero_add]

theorem IsDownwardCap.firstWall_verticalExtrusion {U : Set Plane}
    (hU : IsDownwardCap U) {ε θ : ℝ} (hε : 0 ≤ ε) (hs : 0 < Real.sin θ)
    (x : ℝ) : firstWall (verticalExtrusion U ε) θ x = firstWall U θ x + ε := by
  rw [firstWall, firstWall, hU.support_verticalExtrusion hε (v := unitNormal θ) hs.le]
  field_simp
  simp only [unitNormal]
  ring

theorem IsDownwardCap.cornerWall_verticalExtrusion {U : Set Plane}
    (hU : IsDownwardCap U) {ε θ : ℝ} (hε : 0 ≤ ε)
    (hs : 0 < Real.sin θ) (hc : 0 < Real.cos θ) (x : ℝ) :
    cornerWall (verticalExtrusion U ε) θ x = cornerWall U θ x + ε := by
  rw [cornerWall, cornerWall, hU.firstWall_verticalExtrusion hε hs, secondWall, secondWall,
    hU.support_verticalExtrusion hε (v := companionNormal θ) hc.le, ← min_add_add_right]
  congr 1
  field_simp
  simp only [companionNormal]
  ring

/-- The full terminal wall gains exactly `ε`; clipping the swept supremum at
zero gains at most `ε`. Both parts therefore satisfy the same upper bound. -/
theorem IsDownwardCap.partialBarrier_verticalExtrusion_le {U : Set Plane}
    (hU : IsDownwardCap U) {ε α : ℝ} (hε : 0 ≤ ε)
    (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) (x : ℝ) :
    partialBarrier (verticalExtrusion U ε) α x ≤ partialBarrier U α x + ε := by
  have hswept : sweptNiche (verticalExtrusion U ε) α x ≤ sweptNiche U α x + ε := by
    refine sweptNiche_le_of_forall hα0 (add_nonneg (sweptNiche_nonneg U α x) hε) fun θ hθ => ?_
    obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ⟨hθ.1, hθ.2.trans_le hα⟩
    rw [hU.cornerWall_verticalExtrusion hε hs hc]
    exact add_le_add_left
      (cornerWall_le_sweptNiche (sweptWallValues_bddAbove hU.isCompact hα x) hθ) ε
  refine max_le (hswept.trans (add_le_add_left (le_max_left _ _) ε)) ?_
  rw [hU.firstWall_verticalExtrusion hε
    (Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [hα, Real.pi_pos]))]
  exact add_le_add_left (le_max_right _ _) ε

/-- The charged exterior roof gains exactly the extrusion height, so the score gains half the
width times the height, less the gain of the middle barrier. -/
theorem IsDownwardCap.capScore_verticalExtrusion {U : Set Plane} (hU : IsDownwardCap U) {ε : ℝ}
    (hε : 0 ≤ ε) (α : ℝ) :
    capScore (verticalExtrusion U ε) α = capScore U α + capWidth U / 2 * ε -
      ((∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
          partialBarrier (verticalExtrusion U ε) α x) -
        ∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
          partialBarrier U α x) := by
  have hprojection := hU.horizontalProjection_verticalExtrusion hε
  rw [capScore_eq_integrals, capScore_eq_integrals, show horizontalLeft (verticalExtrusion U ε) =
    horizontalLeft U from congrArg sInf hprojection, show horizontalRight (verticalExtrusion U ε) =
    horizontalRight U from congrArg sSup hprojection]
  have hproj := hU.horizontalProjection_eq_Icc
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hconst : IntegrableOn (fun _ : ℝ => ε) (Icc (horizontalLeft U) (horizontalRight U)) :=
    integrableOn_const measure_Icc_lt_top.ne
  rw [setIntegral_congr_fun (measurableSet_Icc.diff (measurableSet_middleHalfInterval _ _))
    fun x hx => hU.capRoof_verticalExtrusion hε (hproj ▸ hx.1),
    integral_add ((hU.integrableOn_capRoof_Icc _ _).mono_set sdiff_subset)
      (hconst.mono_set sdiff_subset), setIntegral_const, smul_eq_mul,
    volumeReal_exterior_middleHalfInterval hlr, capWidth]
  ring

/-- Equal window lengths pay for the entire barrier increase, even when a
previously zero portion of the niche becomes positive. -/
theorem IsDownwardCap.capScore_le_verticalExtrusion {U : Set Plane}
    (hU : IsDownwardCap U) {ε α : ℝ} (hε : 0 ≤ ε)
    (hheight : ∀ p ∈ U, p.2 + ε ≤ 1)
    (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) :
    capScore U α ≤ capScore (verticalExtrusion U ε) α := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hJ := middleHalfInterval_subset hlr
  have hconst : IntegrableOn (fun _ : ℝ => ε)
      (middleHalfInterval (horizontalLeft U) (horizontalRight U)) :=
    integrableOn_const ((measure_mono hJ).trans_lt measure_Icc_lt_top).ne
  have hbarrier := (integrableOn_partialBarrier_Icc hU.isCompact hα0 hα _ _).mono_set hJ
  have hmiddle := integral_mono ((integrableOn_partialBarrier_Icc
    (hU.isDownwardCap_verticalExtrusion hε hheight).isCompact hα0 hα _ _).mono_set hJ)
    (hbarrier.add hconst) fun x => hU.partialBarrier_verticalExtrusion_le hε hα0 hα x
  simp only [Pi.add_apply] at hmiddle
  rw [integral_add hbarrier hconst, setIntegral_const, smul_eq_mul,
    volumeReal_middleHalfInterval hlr] at hmiddle
  rw [hU.capScore_verticalExtrusion hε, capWidth]
  linarith

/-- Height is the actual attained upward support. -/
def capHeight (U : Set Plane) : ℝ := support U (0, 1)

theorem IsDownwardCap.capHeight_le_one {U : Set Plane} (hU : IsDownwardCap U) :
    capHeight U ≤ 1 := hU.support_upward_le_one

theorem IsDownwardCap.snd_le_capHeight {U : Set Plane} (hU : IsDownwardCap U)
    {p : Plane} (hp : p ∈ U) : p.2 ≤ capHeight U := by
  simpa only [capHeight, coordDot, mul_zero, mul_one, zero_add] using
    coordDot_le_support hU.isCompact hp ((0, 1) : Plane)

/-- The canonical height-one enlargement, defined without selecting a top point. -/
def heightSaturation (U : Set Plane) : Set Plane := verticalExtrusion U (1 - capHeight U)

theorem IsDownwardCap.isDownwardCap_heightSaturation {U : Set Plane}
    (hU : IsDownwardCap U) : IsDownwardCap (heightSaturation U) :=
  hU.isDownwardCap_verticalExtrusion (sub_nonneg.mpr hU.capHeight_le_one) fun p hp => by
    linarith [hU.snd_le_capHeight hp]

theorem IsDownwardCap.horizontalProjection_heightSaturation {U : Set Plane}
    (hU : IsDownwardCap U) :
    horizontalProjection (heightSaturation U) = horizontalProjection U :=
  hU.horizontalProjection_verticalExtrusion (sub_nonneg.mpr hU.capHeight_le_one)

theorem IsDownwardCap.capHeight_heightSaturation {U : Set Plane}
    (hU : IsDownwardCap U) : capHeight (heightSaturation U) = 1 := by
  rw [capHeight, heightSaturation,
    hU.support_verticalExtrusion (sub_nonneg.mpr hU.capHeight_le_one) zero_le_one, capHeight]
  ring

theorem IsDownwardCap.capScore_le_heightSaturation {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) :
    capScore U α ≤ capScore (heightSaturation U) α :=
  hU.capScore_le_verticalExtrusion (sub_nonneg.mpr hU.capHeight_le_one)
    (fun p hp => by linarith [hU.snd_le_capHeight hp]) hα0 hα

end AmbidextrousSofa
