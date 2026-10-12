module

public import AmbidextrousSofa.Analysis.TiltedInitialEnergyBounds

@[expose] public section

/-!
# Exact stopping bounds for a proper reflected excess

The first-zero and decay roots are compared jointly. Differences of
squares show that the decay gain under increasing width pays for the
opposite movement of the first zero. The analogous height comparison
uses the circle relation between those roots. At the largest width,
every energy root is at least two, so the whole height range compares
with its upper endpoint. No subdivision of the height range is needed.
-/

noncomputable section

namespace AmbidextrousSofa.Analysis

def quadraticExcessLength (ε : ℝ) : ℝ := Real.sqrt (1 + 4 * ε) - 1

theorem quadraticExcessLength_nonneg {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ quadraticExcessLength ε :=
  sub_nonneg.2 (Real.one_le_sqrt.2 (by linarith))

theorem quadraticExcessLength_identity {ε : ℝ} (hε : 0 ≤ ε) :
    ε = quadraticExcessLength ε / 2 + quadraticExcessLength ε ^ 2 / 4 := by
  unfold quadraticExcessLength
  linear_combination -Real.sq_sqrt (show 0 ≤ 1 + 4 * ε by linarith) / 4

theorem quadraticExcessLength_lt {ε l : ℝ} (hε : 0 ≤ ε) (hl : 0 ≤ l)
    (hbound : ε < l / 2 + l ^ 2 / 4) : quadraticExcessLength ε < l := by
  have := quadraticExcessLength_identity hε
  nlinarith [quadraticExcessLength_nonneg hε]

/-- A positive decreasing quadratic at the first crossing forces that
crossing to precede any point where the quadratic is already negative. -/
theorem first_zero_lt_of_quadratic {a A d e : ℝ}
    (had : a ≤ d) (hAd : A ≤ d)
    (hquad : 0 ≤ e - d * a + a ^ 2 / 2)
    (hnegative : e - d * A + A ^ 2 / 2 < 0) : a < A := by
  by_contra! h
  nlinarith [mul_nonneg (sub_nonneg.2 h) (by linarith : 0 ≤ 2 * d - a - A)]

def properCrossingRoot (d e : ℝ) : ℝ := Real.sqrt (d ^ 2 - 2 * e)

def properEnergyRoot (d e δ : ℝ) : ℝ := Real.sqrt (d ^ 2 - e * (1 - e) + δ)

def properDecayRoot (d e δ : ℝ) : ℝ := Real.sqrt (4 * properEnergyRoot d e δ - 7)

def properFirstZeroTime (d e : ℝ) : ℝ := d - properCrossingRoot d e

def properDecayLength (d e δ : ℝ) : ℝ := properDecayRoot d e δ - 1

def properExcessEnd (d e δ : ℝ) : ℝ := properFirstZeroTime d e + properDecayLength d e δ

/-- Bound the crossing and decay together by their exact roots. -/
theorem first_zero_add_quadratic_excess_le {d e δ a ε : ℝ}
    (had : a ≤ d)
    (hquad : 0 ≤ e - d * a + a ^ 2 / 2)
    (henergy : (2 + ε) ^ 2 ≤ d ^ 2 - e * (1 - e) + δ) :
    a + quadraticExcessLength ε ≤ properExcessEnd d e δ := by
  have ha : a ≤ properFirstZeroTime d e := by
    have hs : Real.sqrt (d ^ 2 - 2 * e) ≤ d - a :=
      (Real.sqrt_le_left (by linarith)).mpr (by nlinarith only [hquad])
    unfold properFirstZeroTime properCrossingRoot
    linarith only [hs]
  have hy : 2 + ε ≤ properEnergyRoot d e δ :=
    Real.le_sqrt_of_sq_le henergy
  have hz : quadraticExcessLength ε ≤ properDecayLength d e δ := by
    unfold quadraticExcessLength properDecayLength properDecayRoot
    exact sub_le_sub_right (Real.sqrt_le_sqrt (by linarith only [hy])) 1
  exact add_le_add ha hz

theorem properExcess_roots_bounds {d e δ : ℝ}
    (hd0 : (2 - 1 / 2 ^ 6) ≤ d) (hd1 : d ≤ (3 * (37 / 50) + (3 / 8) / 4))
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ (3 / 8) ^ 2 / 4) :
    (11 / 8 ≤ properCrossingRoot d e ∧ properCrossingRoot d e ≤ d ∧
      properCrossingRoot d e ^ 2 = d ^ 2 - 2 * e) ∧
    (19 / 10 ≤ properEnergyRoot d e δ ∧ properEnergyRoot d e δ ≤ 7 / 3 ∧
      properEnergyRoot d e δ ^ 2 = d ^ 2 - e * (1 - e) + δ) ∧
    (3 / 4 ≤ properDecayRoot d e δ ∧ properDecayRoot d e δ ≤ 8 / 5 ∧
      properDecayRoot d e δ ^ 2 = 4 * properEnergyRoot d e δ - 7) := by
  have hd2 := pow_le_pow_left₀ (by norm_num) hd0 2
  have hd2' := pow_le_pow_left₀ (by linarith) hd1 2
  have he2 := mul_nonneg he0 (sub_nonneg.2 he1)
  have he2' : e * (1 - e) ≤ 1 / 4 := by linarith [sq_nonneg (e - 1 / 2)]
  have hy : 19 / 10 ≤ properEnergyRoot d e δ ∧ properEnergyRoot d e δ ≤ 7 / 3 :=
    ⟨Real.le_sqrt_of_sq_le (by linarith), (Real.sqrt_le_left (by norm_num)).2 (by linarith)⟩
  exact ⟨⟨Real.le_sqrt_of_sq_le (by linarith), (Real.sqrt_le_left (by linarith)).2 (by linarith),
      Real.sq_sqrt (by linarith)⟩, ⟨hy.1, hy.2, Real.sq_sqrt (by linarith)⟩,
    ⟨Real.le_sqrt_of_sq_le (by linarith), (Real.sqrt_le_left (by norm_num)).2 (by linarith),
      Real.sq_sqrt (by linarith)⟩⟩

theorem properExcessEnd_mono_width {d D e δ : ℝ}
    (hd0 : (2 - 1 / 2 ^ 6) ≤ d) (hdD : d ≤ D) (hD1 : D ≤ (3 * (37 / 50) + (3 / 8) / 4))
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ (3 / 8) ^ 2 / 4) :
    properExcessEnd d e δ ≤ properExcessEnd D e δ := by
  obtain ⟨⟨hx0, -, hx2⟩, ⟨hy0, hy1, hy2⟩, ⟨hz0, hz1, hz2⟩⟩ :=
    properExcess_roots_bounds hd0 (hdD.trans hD1) he0 he1 hδ0 hδ1
  obtain ⟨⟨hX0, -, hX2⟩, ⟨hY0, hY1, hY2⟩, ⟨hZ0, hZ1, hZ2⟩⟩ :=
    properExcess_roots_bounds (hd0.trans hdD) hD1 he0 he1 hδ0 hδ1
  unfold properExcessEnd properFirstZeroTime properDecayLength
  generalize properCrossingRoot d e = x, properCrossingRoot D e = X, properEnergyRoot d e δ = y,
    properEnergyRoot D e δ = Y, properDecayRoot d e δ = z, properDecayRoot D e δ = Z at *
  -- The crossing root moves by at most `2 (D - d)`, the decay root by at least `D - d`.
  have hX : (X - x) * (X + x) ≤ 2 * (D - d) * (X + x) := by
    linarith only [hx2, hX2, mul_nonneg (sub_nonneg.2 hdD)
      (by linarith only [hx0, hX0, hdD, hD1] : 0 ≤ 2 * (X + x) - D - d)]
  have hY : 4 / 5 * (D - d) * (Y + y) ≤ (Y - y) * (Y + y) := by
    linarith only [hy2, hY2, mul_nonneg (sub_nonneg.2 hdD)
      (by linarith only [hy1, hY1, hd0, hdD] : 0 ≤ D + d - 4 / 5 * (Y + y))]
  replace hY := le_of_mul_le_mul_right hY (by linarith only [hy0, hY0])
  have hZ : 5 / 4 * (Y - y) * (Z + z) ≤ (Z - z) * (Z + z) := by
    linarith only [hz2, hZ2, mul_nonneg (by linarith only [hY, hdD] : 0 ≤ Y - y)
      (by linarith only [hz1, hZ1] : 0 ≤ 4 - 5 / 4 * (Z + z))]
  linarith only [hY, hdD, le_of_mul_le_mul_right hX (by linarith only [hx0, hX0]),
    le_of_mul_le_mul_right hZ (by linarith only [hz0, hZ0])]

theorem properExcessEnd_mono_height {d e E δ : ℝ}
    (hd0 : (2 - 1 / 2 ^ 6) ≤ d) (hd1 : d ≤ (3 * (37 / 50) + (3 / 8) / 4))
    (he0 : 0 ≤ e) (heE : e ≤ E) (hE1 : E ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ (3 / 8) ^ 2 / 4)
    (henergy : 4 ≤ d ^ 2 - 1 / 4 + δ) :
    properExcessEnd d e δ ≤ properExcessEnd d E δ := by
  obtain ⟨⟨hx0, -, hx2⟩, ⟨-, -, hy2⟩, ⟨-, -, hz2⟩⟩ :=
    properExcess_roots_bounds hd0 hd1 he0 (heE.trans hE1) hδ0 hδ1
  obtain ⟨⟨hX0, -, hX2⟩, ⟨-, -, hY2⟩, ⟨-, -, hZ2⟩⟩ :=
    properExcess_roots_bounds hd0 hd1 (he0.trans heE) hE1 hδ0 hδ1
  have hy0 : 2 ≤ properEnergyRoot d e δ := Real.le_sqrt_of_sq_le
    (by nlinarith only [henergy, sq_nonneg (e - 1 / 2)])
  have hY0 : 2 ≤ properEnergyRoot d E δ := Real.le_sqrt_of_sq_le
    (by nlinarith only [henergy, sq_nonneg (E - 1 / 2)])
  have hz0 : 1 ≤ properDecayRoot d e δ := Real.le_sqrt_of_sq_le (by linarith only [hy0])
  have hZ0 : 1 ≤ properDecayRoot d E δ := Real.le_sqrt_of_sq_le (by linarith only [hY0])
  unfold properExcessEnd properFirstZeroTime properDecayLength
  generalize properCrossingRoot d e = x, properCrossingRoot d E = X, properEnergyRoot d e δ = y,
    properEnergyRoot d E δ = Y, properDecayRoot d e δ = z, properDecayRoot d E δ = Z at *
  have hyx : x ≤ y := by nlinarith only [hx2, hy2, hx0, hy0, he0, hδ0, sq_nonneg e]
  have hYX : X ≤ Y := by nlinarith only [hX2, hY2, hX0, hY0, he0, heE, hδ0, sq_nonneg E]
  have hxX : 0 ≤ x - X := by nlinarith only [hx2, hX2, hx0, hX0, heE]
  -- The energy roots dominate the crossing roots; both decay roots are at least one.
  have hden : 2 * (x + X) ≤ (y + Y) * (z + Z) := by
    nlinarith only [hyx, hYX, hy0, hY0, hz0, hZ0,
      mul_nonneg (by linarith only [hz0, hZ0] : 0 ≤ z + Z - 2)
        (by linarith only [hy0, hY0] : 0 ≤ y + Y)]
  have hcross : (x - X) * (x + X) = 2 * (E - e) := by linarith only [hx2, hX2]
  have henergy' : (Y - y) * (Y + y) = (E - e) * (E + e - 1) := by
    nlinarith only [hy2, hY2]
  have hdecay : (Z - z) * (Z + z) = 4 * (Y - y) := by linarith only [hz2, hZ2]
  -- Clear the positive denominators in the two differences of squares.
  have hbalance : (x - X + Z - z) * (Z + z) * (Y + y) =
      (x - X) * ((Z + z) * (Y + y) - 2 * (x + X)) + 4 * (E - e) * (E + e) := by
    linear_combination (Y + y) * hdecay + 4 * henergy' + 2 * hcross
  have hnonneg : 0 ≤ (x - X + Z - z) * (Z + z) * (Y + y) := by
    rw [hbalance]
    exact add_nonneg (mul_nonneg hxX (by linarith only [hden]))
      (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr heE)) (by linarith only [he0, heE]))
  have hfirst : 0 * (Z + z) ≤ (x - X + Z - z) * (Z + z) :=
    le_of_mul_le_mul_right (by simpa only [zero_mul] using hnonneg)
      (by linarith only [hy0, hY0])
  have hsecond : 0 ≤ x - X + Z - z :=
    le_of_mul_le_mul_right hfirst (by linarith only [hz0, hZ0])
  linarith only [hsecond]

theorem properFirstZeroTime_quadratic {d e : ℝ}
    (hrad : 0 ≤ d ^ 2 - 2 * e) :
    e - d * properFirstZeroTime d e + properFirstZeroTime d e ^ 2 / 2 = 0 := by
  unfold properFirstZeroTime properCrossingRoot
  linear_combination Real.sq_sqrt hrad / 2

theorem properFirstZeroTime_lt_of_quadratic {d e T : ℝ}
    (hrad : 0 ≤ d ^ 2 - 2 * e) (hTd : T ≤ d)
    (hnegative : e - d * T + T ^ 2 / 2 < 0) : properFirstZeroTime d e < T :=
  first_zero_lt_of_quadratic (sub_le_self _ (Real.sqrt_nonneg _)) hTd
    (properFirstZeroTime_quadratic hrad).ge hnegative

theorem properDecayLength_lt_of_energy {d e δ ell : ℝ} (hell : 0 ≤ ell)
    (hbound : d ^ 2 - e * (1 - e) + δ < (2 + ell / 2 + ell ^ 2 / 4) ^ 2) :
    properDecayLength d e δ < ell := by
  have hy : properEnergyRoot d e δ < 2 + ell / 2 + ell ^ 2 / 4 :=
    (Real.sqrt_lt' (by positivity)).2 hbound
  have hz : properDecayRoot d e δ < ell + 1 := (Real.sqrt_lt' (by linarith)).2 (by linarith)
  unfold properDecayLength
  linarith

/-- First increase width to `D`, then height to `E`. If every energy at width `D` is
at least four, the entire parameter box reduces to this one corner. -/
theorem properExcessEnd_lt_of_corner {d e δ D E T L B : ℝ}
    (hd0 : (2 - 1 / 2 ^ 6) ≤ d) (hdD : d ≤ D) (hD : D ≤ (3 * (37 / 50) + (3 / 8) / 4))
    (he0 : 0 ≤ e) (heE : e ≤ E) (hE : E ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ (3 / 8) ^ 2 / 4)
    (hTD : T ≤ D) (hT : E - D * T + T ^ 2 / 2 < 0) (hL : 0 ≤ L)
    (henergy : D ^ 2 - E * (1 - E) + δ < (2 + L / 2 + L ^ 2 / 4) ^ 2)
    (hDenergy : 4 ≤ D ^ 2 - 1 / 4 + δ) (hTL : T + L ≤ B) :
    properExcessEnd d e δ < B := by
  have hD2 := pow_le_pow_left₀ (by norm_num) (hd0.trans hdD) 2
  have ht := properFirstZeroTime_lt_of_quadratic (by linarith) hTD hT
  have hl := properDecayLength_lt_of_energy hL henergy
  have hcorner := (properExcessEnd_mono_width hd0 hdD hD he0 (heE.trans hE) hδ0 hδ1).trans
    (properExcessEnd_mono_height (hd0.trans hdD) hD he0 heE hE hδ0 hδ1 hDenergy)
  unfold properExcessEnd at *
  linarith only [hcorner, ht, hl, hTL]

/-- The zero-tilt baseline stops before endpoint contact, for the full reflected height range. -/
theorem zero_tilt_excess_stops_early {d e : ℝ}
    (hd0 : 2 ≤ d) (hd1 : d ≤ 111 / 50) (he0 : 0 ≤ e) (he1 : e ≤ 3 / 4) :
    properExcessEnd d e 0 < 11 / 15 :=
  properExcessEnd_lt_of_corner (D := 111 / 50) (E := 3 / 4) (T := 2 / 5) (L := 1 / 3)
    (by linarith only [hd0]) hd1 (by norm_num) he0 he1 (by norm_num) le_rfl
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end AmbidextrousSofa.Analysis
