module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

@[expose] public section

open Finset Classical

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem jacobi_congr {a b s : ℕ} (h : a ≡ b [MOD s]) : jacobiSym (a : ℤ) s = jacobiSym (b : ℤ) s := by
  rw [jacobiSym.mod_left (a : ℤ), jacobiSym.mod_left (b : ℤ)]
  have h' : a % s = b % s := h
  rw [← Int.natCast_mod, ← Int.natCast_mod, h']

theorem exists_jacobi_neg_one (m t : ℕ) (ht : Odd t) (hsq : Squarefree t) (h1 : 1 < t)
    (hc : t.Coprime m) : ∃ u : ℕ, u ≡ 1 [MOD m] ∧ jacobiSym (u : ℤ) t = -1 := by
  obtain ⟨p, hp, hpt⟩ := Nat.exists_prime_and_dvd (show t ≠ 1 by omega)
  haveI := Fact.mk hp
  obtain ⟨t', rfl⟩ := hpt
  have ht0 : t' ≠ 0 := by
    rintro rfl
    simp at h1
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr ht) (even_two_mul t')
  have hpt' : ¬ p ∣ t' := by
    rintro ⟨k, rfl⟩
    have := hsq p ⟨k, by ring⟩
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp this)
  have hcp : p.Coprime t' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpt'
  have hpm : p.Coprime m := Nat.Coprime.coprime_dvd_left (Dvd.intro t' rfl) hc
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p)
    (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder (Nat.Coprime.mul_right hcp hpm) a.val 1
  refine ⟨k, Nat.ModEq.of_mul_left t' hk2, ?_⟩
  haveI : NeZero t' := ⟨ht0⟩
  rw [jacobiSym.mul_right, jacobi_congr hk1, jacobi_congr (Nat.ModEq.of_mul_right m hk2),
    ← jacobiSym.legendreSym.to_jacobiSym p, (legendreSym.eq_neg_one_iff p).mpr (by simpa using ha)]
  simp

private theorem dvd_of_jacobiSym_agree_on_residue_class (m₀ s₁ s₂ : ℕ) (h1 : Odd s₁) (h2 : Odd s₂)
    (hq1 : Squarefree s₁) (hc1 : s₁.Coprime m₀)
    (h : ∀ u : ℕ, u % m₀ = 1 % m₀ → u.Coprime (s₁ * s₂) → jacobiSym (u : ℤ) s₁ = jacobiSym (u : ℤ) s₂) :
    s₁ ∣ s₂ := by
  by_contra hnd
  have hs1 : s₁ ≠ 0 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr h1) ⟨0, rfl⟩
  have hs2 : s₂ ≠ 0 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr h2) ⟨0, rfl⟩
  have hgd : Nat.gcd s₁ s₂ ∣ s₁ := Nat.gcd_dvd_left s₁ s₂
  have hg0 : Nat.gcd s₁ s₂ ≠ 0 := Nat.gcd_ne_zero_left hs1
  have hga : Nat.gcd s₁ s₂ * (s₁ / Nat.gcd s₁ s₂) = s₁ := Nat.mul_div_cancel' hgd
  have hgb : Nat.gcd s₁ s₂ * (s₂ / Nat.gcd s₁ s₂) = s₂ := Nat.mul_div_cancel' (Nat.gcd_dvd_right s₁ s₂)
  set g := Nat.gcd s₁ s₂ with hg
  set a := s₁ / g with ha
  set b := s₂ / g with hb
  have ha0 : a ≠ 0 := by
    rintro h0
    rw [h0, mul_zero] at hga
    exact hs1 hga.symm
  have ha1 : a ≠ 1 := by
    rintro h0
    rw [h0, mul_one] at hga
    exact hnd (hga ▸ Nat.gcd_dvd_right s₁ s₂)
  have hadv : a ∣ s₁ := Dvd.intro_left g hga
  have hao : Odd a := Odd.of_dvd_nat h1 hadv
  have haq : Squarefree a := Squarefree.squarefree_of_dvd hadv hq1
  have hag : a.Coprime g := by
    have := hq1
    rw [← hga] at this
    exact (Nat.squarefree_mul_iff.mp this).1.symm
  have hab : a.Coprime b := Nat.coprime_div_gcd_div_gcd (Nat.pos_of_ne_zero hg0)
  have has2 : a.Coprime s₂ := by
    rw [← hgb]
    exact Nat.Coprime.mul_right hag hab
  have ham : a.Coprime m₀ := Nat.Coprime.coprime_dvd_left hadv hc1
  obtain ⟨u, hu1, hJ⟩ := exists_jacobi_neg_one (m₀ * s₂) a hao haq
    (lt_of_le_of_ne (Nat.pos_of_ne_zero ha0) (Ne.symm ha1))
    (Nat.Coprime.mul_right ham has2)
  have hum : u ≡ 1 [MOD m₀] := Nat.ModEq.of_mul_right s₂ hu1
  have hus : u ≡ 1 [MOD s₂] := Nat.ModEq.of_mul_left m₀ hu1
  have hug : u ≡ 1 [MOD g] := Nat.ModEq.of_dvd (Nat.gcd_dvd_right s₁ s₂) hus
  haveI : NeZero g := ⟨hg0⟩
  haveI : NeZero a := ⟨ha0⟩
  have hJs : jacobiSym (u : ℤ) s₂ = 1 := by
    rw [jacobi_congr hus]
    simp
  have hJg : jacobiSym (u : ℤ) g = 1 := by
    rw [jacobi_congr hug]
    simp
  have hJ1 : jacobiSym (u : ℤ) s₁ = -1 := by
    rw [← hga, jacobiSym.mul_right, hJg, hJ]
    ring
  have hua : u.Coprime a := by
    by_contra hn
    have h0 : jacobiSym (u : ℤ) a = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime, Int.gcd_natCast_natCast]
      exact hn
    rw [h0] at hJ
    norm_num at hJ
  have hus' : u.Coprime s₂ := by
    have e : Nat.gcd u s₂ = Nat.gcd 1 s₂ := Nat.ModEq.gcd_eq hus
    rw [Nat.gcd_one_left] at e
    exact e
  have hug' : u.Coprime g := Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right s₁ s₂) hus'
  have hus1 : u.Coprime s₁ := by
    rw [← hga]
    exact Nat.Coprime.mul_right hug' hua
  have := h u hum (Nat.Coprime.mul_right hus1 hus')
  rw [hJ1, hJs] at this
  norm_num at this

theorem jacobi_separate (m₀ s₁ s₂ : ℕ) (hm : 0 < m₀) (h1 : Odd s₁) (h2 : Odd s₂) (hq1 : Squarefree s₁)
    (hq2 : Squarefree s₂) (hc1 : s₁.Coprime m₀) (hc2 : s₂.Coprime m₀)
    (h : ∀ u : ℕ, u % m₀ = 1 % m₀ → u.Coprime (s₁ * s₂) → jacobiSym (u : ℤ) s₁ = jacobiSym (u : ℤ) s₂) :
    s₁ = s₂ := by
  apply Nat.dvd_antisymm
  · exact dvd_of_jacobiSym_agree_on_residue_class m₀ s₁ s₂ h1 h2 hq1 hc1 h
  · exact dvd_of_jacobiSym_agree_on_residue_class m₀ s₂ s₁ h2 h1 hq2 hc2
      (fun u hu hc => (h u hu (by rwa [mul_comm])).symm)

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
