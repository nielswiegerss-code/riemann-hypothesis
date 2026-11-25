module

public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.RestValBdG
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.FrMemLetters

@[expose] public section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section Ord2

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {L₁ N₁ : ℕ}

theorem posU_lt_iff' (hV : Fr.Valid L₁ N₁) (j : ℤ) (N : ℕ) (hN : N = (Fr.LLset j).card) (a b : ℕ) (ha : a < N + r)
    (hb : b < N + r) : posU Fr N j a < posU Fr N j b ↔ a < b := by
  subst hN; exact posU_lt_iff hV j a b ha hb

theorem posU_le_iff' (hV : Fr.Valid L₁ N₁) (j : ℤ) (N : ℕ) (hN : N = (Fr.LLset j).card) (a b : ℕ) (ha : a < N + r)
    (hb : b < N + r) : posU Fr N j a ≤ posU Fr N j b ↔ a ≤ b := by
  subst hN; exact posU_le_iff hV j a b ha hb

theorem posU_ll' (j : ℤ) (N : ℕ) (l : ℕ) (hl : l < N) : posU Fr N j l = llPos Fr j l := by
  unfold posU
  rw [ite_eq_left hl]

theorem posU_fr' (j : ℤ) (N : ℕ) (i : ℕ) : posU Fr N j (N + i) = Fr.fr j i := by
  unfold posU
  rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]

theorem w_lt_posU' (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (N : ℕ) (hN : N = (Fr.LLset j).card) (i u : ℕ) (hi : i < r)
    (hu : u < N + r) : Fr.fr (j - 1) i < posU Fr N j u := by
  subst hN; exact w_lt_posU hV hr j i u hi hu

end Ord2

section Pre

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {L₁ N₁ : ℕ} {J : ℕ} {nL : ZMod J → ℕ}

theorem ml_ll_lt (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) (j' : ZMod J) (l : Fin (nL j')) :
    mlPos Fr nL (ML.ll j' l) ∈ SLt j (posU Fr (nL j) (segZ j) u) ↔ j' = j ∧ l.val < u := by
  show (j' = j ∧ llPos Fr (segZ j') l.val < _) ↔ _
  refine and_congr_right fun h => ?_
  rw [← h] at hu ⊢
  rw [← posU_ll' (Fr := Fr) (segZ j') (nL j') l.val l.isLt]
  exact posU_lt_iff' hV (segZ j') (nL j') (hnL j') l.val u (by omega) hu

theorem ml_ll_le (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) (j' : ZMod J) (l : Fin (nL j')) :
    mlPos Fr nL (ML.ll j' l) ∈ SLe j (posU Fr (nL j) (segZ j) u) ↔ j' = j ∧ l.val ≤ u := by
  show (j' = j ∧ llPos Fr (segZ j') l.val ≤ _) ↔ _
  refine and_congr_right fun h => ?_
  rw [← h] at hu ⊢
  rw [← posU_ll' (Fr := Fr) (segZ j') (nL j') l.val l.isLt]
  exact posU_le_iff' hV (segZ j') (nL j') (hnL j') l.val u (by omega) hu

theorem fr_lt (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) (j' : ZMod J) (m : Fin r) :
    (j' = j ∧ Fr.fr (segZ j') (r - 1 - m.val) < posU Fr (nL j) (segZ j) u) ↔ j' = j ∧ nL j + (r - 1 - m.val) < u := by
  have hm := m.isLt
  refine and_congr_right fun h => ?_
  rw [← h] at hu ⊢
  rw [← posU_fr' (Fr := Fr) (segZ j') (nL j')]
  exact posU_lt_iff' hV _ _ (hnL j') _ u (by omega) hu

theorem fr_le (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) (j' : ZMod J) (m : Fin r) :
    (j' = j ∧ Fr.fr (segZ j') (r - 1 - m.val) ≤ posU Fr (nL j) (segZ j) u) ↔ j' = j ∧ nL j + (r - 1 - m.val) ≤ u := by
  have hm := m.isLt
  refine and_congr_right fun h => ?_
  rw [← h] at hu ⊢
  rw [← posU_fr' (Fr := Fr) (segZ j') (nL j')]
  exact posU_le_iff' hV _ _ (hnL j') _ u (by omega) hu

private theorem mem_NSet_left (j j' : ZMod J) (l : Fin (nL j')) (u : ℕ) :
    (⟨j', Sum.inl l⟩ : TL J nL r) ∈ NSet nL j u ↔ j' = j ∧ l.val < u := by
  constructor
  · rintro (⟨l', he, h⟩ | ⟨m', he, _⟩) <;>
      obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.mp he <;> cases he2
    exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩
    exact Or.inl ⟨l, rfl, h⟩

private theorem mem_NSet_right (j j' : ZMod J) (m : Fin r) (u : ℕ) :
    (⟨j', Sum.inr m⟩ : TL J nL r) ∈ NSet nL j u ↔ j' = j ∧ nL j + (r - 1 - m.val) < u := by
  constructor
  · rintro (⟨l', he, _⟩ | ⟨m', he, h⟩) <;>
      obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.mp he <;> cases he2
    exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩
    exact Or.inr ⟨m, rfl, h⟩

theorem tl_pre_lt (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) : tlPos Fr nL ⁻¹' SLt j (posU Fr (nL j) (segZ j) u) = NSet nL j u := by
  ext ⟨j', l | m⟩
  · rw [Set.mem_preimage]
    exact (ml_ll_lt hV hnL j u hu j' l).trans (mem_NSet_left j j' l u).symm
  · rw [Set.mem_preimage]
    exact (fr_lt hV hnL j u hu j' m).trans (mem_NSet_right j j' m u).symm

theorem tl_pre_le (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) : tlPos Fr nL ⁻¹' SLe j (posU Fr (nL j) (segZ j) u) = NSet nL j (u + 1) := by
  ext ⟨j', l | m⟩
  · rw [Set.mem_preimage]
    exact (ml_ll_le hV hnL j u hu j' l).trans
      ((and_congr_right fun _ => Nat.lt_succ_iff.symm).trans
        (mem_NSet_left j j' l (u + 1)).symm)
  · rw [Set.mem_preimage]
    exact (fr_le hV hnL j u hu j' m).trans
      ((and_congr_right fun _ => Nat.lt_succ_iff.symm).trans
        (mem_NSet_right j j' m (u + 1)).symm)

end Pre

end Formalism.MainNotions.Proposition5Numerics
