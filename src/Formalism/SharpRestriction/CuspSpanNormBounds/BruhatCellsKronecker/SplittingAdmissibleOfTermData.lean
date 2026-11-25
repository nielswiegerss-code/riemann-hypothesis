module

public import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
public import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals NumberField Module

section Rec

variable {D : D7} (X : TermTie D)

theorem tie_Tu_pos (D : D7) (u : D.what₂.Word) : 0 < Tu D u := (D.mem u).A.T_prime.pos

theorem tie_Gval_ne {u u' : D.what₂.Word} (t : D.s.Term u u') (h : D.s.Gterm t ≠ 0) :
    Gval (X.fl t) (X.fl' t) ≠ 0 := by
  rw [← X.G_eq t]
  exact (map_ne_zero _).2 h

theorem tie_G_pos {u u' : D.what₂.Word} (t : D.s.Term u u') (h : D.s.Gterm t ≠ 0) (τ : D.host.E →+* ℂ) :
    0 < (τ (Gval (X.fl t) (X.fl' t))).re :=
  (b_G_pos (p_starConj D) (tie_Tu_pos D u) (X.fl t) (X.fl' t) (X.fixed t).2.2.1.2 (X.lift' t).2
    (tie_Gval_ne X t h) (p_posX D _ (tie_Tu_pos D u) (X.fl t)) τ).1

theorem GDr_of_tie : PX.GDr D X := by
  intro u u' t h
  have hpos := tie_G_pos X t h
  refine ⟨fun h1 => ?_, fun _ τ => hpos _⟩

  have hG : Gval (X.fl t) (X.fl' t) = -(((Tu D u : ℕ) : D.host.E) * ((Tu D u' : ℕ) : D.host.E) *
      (Dl (X.fl t).fl (X.fl' t).fl D.R.rS * star (Dl (X.fl t).fl (X.fl' t).fl D.R.rS))) := by
    simp only [Formalism.MainNotions.S.Lat.Gval, Formalism.MainNotions.S.Gflag, h1, star_zero, mul_zero, zero_sub]
  haveI := D.host.isCMField_hostE
  have hc : ∀ y : D.host.E, D.host.φ₀ (star y) = starRingEnd ℂ (D.host.φ₀ y) := fun y =>
    NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ y
  have h0 := hpos D.host.φ₀
  rw [hG, map_neg, map_mul, map_mul, map_mul, map_natCast, map_natCast, hc, Complex.mul_conj] at h0
  have key : 0 ≤ ((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ) *
      Complex.normSq (D.host.φ₀ (Dl (X.fl t).fl (X.fl' t).fl D.R.rS)) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Complex.normSq_nonneg _)
  simp at h0
  linarith

end Rec

theorem tie_Dl_eq' {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
    (F : FlagG S r T) (F' : FlagG S r T') (j : ℕ) (hj : j ≤ r + 1) :
    Dl F F' j = ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj)).det := by
  unfold Formalism.MainNotions.S.Dl Formalism.MainNotions.S.leadMinorE
  rw [dite_eq_left hj]

section Packets

variable {D : D7} (X : TermTie D)

theorem tie_X_le_ker {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (F : FlagG S r T) (y : S.V) (h : ∀ a, S.hT (F.e a) y = 0) : ∀ x ∈ F.X, S.hT x y = 0 := by
  intro x hx
  unfold Formalism.MainNotions.S.FlagG.X at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact h a
  | zero => simp
  | add x z _ _ hx hz => simp [hx, hz]
  | smul c x _ hx => simp [hx]

end Packets

end Formalism.MainNotions.BridgeLemma
