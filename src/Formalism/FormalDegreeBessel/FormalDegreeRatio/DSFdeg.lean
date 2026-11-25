module

public import Formalism.FormalDegreeBessel.StatementDS
import Mathlib.Tactic.Lemma

@[expose] public section

open Finset

namespace Formalism.QuantumDeterminants

open Formalism.REAL

private lemma fin_sub_pos {n : ℕ} {a b : Fin n} (h : a < b) :
    0 < ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) :=
  sub_pos.mpr (Nat.cast_lt.mpr h)

theorem formal_degree_pos_holds : FdegPos := by
  intro n lam hl
  unfold fdegHC
  apply div_pos
  · refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
    rw [Finset.mem_filter] at hb
    exact abs_pos.mpr (sub_ne_zero.mpr fun h => hb.2.ne (hl h))
  · exact Finset.prod_pos fun a _ => Finset.prod_pos fun b hb =>
      fin_sub_pos (Finset.mem_filter.mp hb).2

end Formalism.QuantumDeterminants
