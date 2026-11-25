module

public import Formalism.SharpRestriction.GrowthBounds.FlipOneThree
import Formalism.SharpRestriction.GrowthBounds.CountingStatementReduction

@[expose] public section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

theorem segDists_lt {n' : ℕ} (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (l u : Fin (segS TT j)) (h : l < u) :
    (segDists TT j).get l < (segDists TT j).get u :=
  (Finset.sortedLT_sort _).strictMono_get h

theorem segDists_lt_G {n' : ℕ} (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (u : Fin (segS TT j)) :
    (segDists TT j).get u < segG TT j := by
  have hm : (segDists TT j).get u ∈ segDists TT j := List.get_mem _ _
  unfold segDists at hm
  rw [Finset.mem_sort, Finset.mem_image] at hm
  obtain ⟨x, hx, hxe⟩ := hm
  rw [Finset.mem_filter] at hx
  have e : (segDists TT j).get u = cdist (segStart TT j) x := hxe.symm
  rw [e]
  exact hx.2.2.2

theorem P_step (l u : Fin X.s) (h : l < u) :
    X.p * (X.S C0 CE1 CE2).P X.p u ≤ (X.S C0 CE1 CE2).P X.p l := by
  have h1 := segDists_lt X.L.TT X.j l u h
  have h2 := segDists_lt_G X.L.TT X.j u
  have hp : 0 < X.p := by
    have := X.std.1.five_le
    show 0 < X.L.p
    omega
  show X.p * X.p ^ (segG X.L.TT X.j - (segDists X.L.TT X.j).get u) ≤
    X.p ^ (segG X.L.TT X.j - (segDists X.L.TT X.j).get l)
  rw [← pow_succ']
  exact Nat.pow_le_pow_right hp (by omega)

theorem p_le_P (u : Fin X.s) : X.p ≤ (X.S C0 CE1 CE2).P X.p u := by
  have h1 := segDists_lt_G X.L.TT X.j u
  have hp : 0 < X.p := by
    have := X.std.1.five_le
    show 0 < X.L.p
    omega
  show X.p ≤ X.p ^ (segG X.L.TT X.j - (segDists X.L.TT X.j).get u)
  calc X.p = X.p ^ 1 := (pow_one _).symm
    _ ≤ _ := Nat.pow_le_pow_right hp (by omega)

end Formalism.MainNotions.G.SymmetricFormBlocks
