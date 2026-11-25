module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JTransM
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FramesTor
public import Formalism.FormalDegreeBessel.StatementBF

@[expose] public section

namespace Formalism.MainNotions.S.Pv.Frames

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S

theorem col_of_fix {m : ℕ} {h : Matrix (Fin m) (Fin m) ℂ} {c : Fin m} (hc : h *ᵥ bvec c = bvec c) (p : Fin m) :
    h p c = if p = c then 1 else 0 := by
  simpa only [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] using congrFun hc p

theorem Hpk_esI_row {k r : ℕ} (a : Fin r) (q : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) q = if q = eI k r a then 1 else 0 := by
  apply _root_.ReciprocityTheory.ChartRestriction.DS.Mult1.TransM.Hpk_esI <;> assumption

theorem Hpk_eI_row {k r : ℕ} (a : Fin r) (q : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) q = if q = esI k r a then 1 else 0 := by
  apply _root_.ReciprocityTheory.ChartRestriction.DS.Mult1.TransM.Hpk_eI <;> assumption

theorem Hpk_mid_col {k r : ℕ} (i j : Fin (2 * r + k + 1)) (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k)
    (hi : i.val < r ∨ r + k < i.val) : Hpk k r i j = 0 := by
  unfold Hpk
  rw [ite_eq_right (fun h => by have := h.1; have := h.2; omega), ite_eq_right (fun h => by have := h.1; omega),
    ite_eq_right (fun h => by have := h.1; have := h.2.1; omega)]

theorem UH_entry {m : ℕ} {H h : Matrix (Fin m) (Fin m) ℂ} (hUH : hᴴ * H * h = H) {c : Fin m}
    (hc : ∀ p, h p c = if p = c then 1 else 0) (j : Fin m) : ∑ q, H c q * h q j = H c j := by
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, hc, apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ] using congrArg (fun M : Matrix (Fin m) (Fin m) ℂ => M c j) hUH

theorem fix_dT {k r : ℕ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hU : h ∈ UH (Hpk k r))
    (hfix : ∀ a : Fin r, h *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ h *ᵥ bvec (esI k r a) = bvec (esI k r a))
    (i j : Fin (2 * r + k + 1)) (hne : h i j ≠ 0) : dT k r i = dT k r j := by
  have hU' : hᴴ * Hpk k r * h = Hpk k r := hU
  by_cases hjl : j.val < r
  · have := col_of_fix (hfix ⟨j.val, hjl⟩).1 i
    rw [show eI k r ⟨j.val, hjl⟩ = j from Fin.ext rfl] at this
    rw [this] at hne
    split_ifs at hne with e
    · rw [e]
    · exact absurd rfl hne
  by_cases hjh : r + k < j.val
  · have ha : 2 * r + k - j.val < r := by omega
    have := col_of_fix (hfix ⟨2 * r + k - j.val, ha⟩).2 i
    rw [show esI k r ⟨2 * r + k - j.val, ha⟩ = j from
      Fin.ext (by show 2 * r + k - (2 * r + k - j.val) = j.val; omega)] at this
    rw [this] at hne
    split_ifs at hne with e
    · rw [e]
    · exact absurd rfl hne
  push Not at hjl hjh
  rw [dT_mid j hjl hjh]
  by_cases hil : i.val < r
  · exfalso
    set a : Fin r := ⟨i.val, hil⟩
    have hcol := col_of_fix (hfix a).2
    have e := UH_entry hU' hcol j
    have s1 : ∑ q, Hpk k r (esI k r a) q * h q j = h (eI k r a) j := by
      simp only [Hpk_esI_row, ite_mul, one_mul, zero_mul]
      simp [Finset.sum_ite_eq']
    rw [s1, Hpk_mid_col _ j hjl hjh (Or.inr (by show r + k < 2 * r + k - i.val; omega))] at e
    rw [show eI k r a = i from Fin.ext rfl] at e
    exact hne e
  by_cases hih : r + k < i.val
  · exfalso
    have ha : 2 * r + k - i.val < r := by omega
    set a : Fin r := ⟨2 * r + k - i.val, ha⟩
    have hcol := col_of_fix (hfix a).1
    have e := UH_entry hU' hcol j
    have s1 : ∑ q, Hpk k r (eI k r a) q * h q j = h (esI k r a) j := by
      simp only [Hpk_eI_row, ite_mul, one_mul, zero_mul]
      simp [Finset.sum_ite_eq']
    rw [s1, Hpk_mid_col _ j hjl hjh (Or.inl (by show (2 * r + k - i.val) < r; omega))] at e
    rw [show esI k r a = i from Fin.ext (by show 2 * r + k - (2 * r + k - i.val) = i.val; omega)] at e
    exact hne e
  push Not at hil hih
  exact dT_mid i hil hih

theorem UW_dT {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) (i j : Fin (2 * r + k + 1)) (hne : h i j ≠ 0) : dT k r i = dT k r j :=
  fix_dT hh.1 hh.2.1 i j hne

theorem UW_conjI {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : tTi k r * h * tT k r = h := conjI_eq_self (UW_dT hh)

theorem conjI_inv {k r : ℕ} (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    tTi k r * M⁻¹ * tT k r = (tTi k r * M * tT k r)⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, tTi_inv, tT_inv, Matrix.mul_assoc]

theorem bigCell_dT {k r : ℕ} (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hne : bigCell k r c μ i j ≠ 0) : dT k r i = dT k r j := by
  unfold bigCell at hne
  split_ifs at hne with h1 h2 h3 h4 h5
  · rw [h2, dT_esI]
    simp [dT, h1]
  · exact absurd rfl hne
  · rw [dT_mid i h4.1 h4.2, dT_mid j (by omega) h3]
  · exact absurd rfl hne
  · exact (dT_pair i j (by omega) (by omega)).symm
  · exact absurd rfl hne

end Formalism.MainNotions.S.Pv.Frames
