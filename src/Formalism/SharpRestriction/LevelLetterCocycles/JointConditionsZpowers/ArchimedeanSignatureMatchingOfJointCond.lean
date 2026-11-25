module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Mathlib.Tactic.Linter.Style

@[expose] public section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

open NumberField IsDedekindDomain

section Roots

variable {g : ℕ} [Fact g.Prime]

theorem card_rootsBar (a : (ZMod g)[X]) : Multiset.card (Formalism.CyclotomicNorms.rootsBar a) = a.natDegree := by
  exact GlobalTheory.TameLabels.card_rootsBar a

end Roots

section Lab

variable (D : D7)
  (hTw : ∀ (k : Fin 2) (w : PlE D.host) (a : D.naut.LP w) (s : ℝ),
    D.naut.items₂ k w (D.naut.lpTw a s) = D.naut.items₂ k w a)

include hTw

end Lab

end Formalism.MainNotions.N
