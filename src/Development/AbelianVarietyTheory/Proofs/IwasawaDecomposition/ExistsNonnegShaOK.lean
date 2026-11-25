module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero
import Mathlib.Tactic.Linter.Style

@[expose] public section

namespace GlobalTheory.MemN
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

theorem shaOK_shaTrue (B : Pre) : ShaOK B (GaloisStage.shaTrue B.host) := by
  refine ⟨fun p _ => GaloisStage.lData B.host p, ?_⟩
  intro p hp e _ _ n h
  rw [GaloisStage.shaTrue, dite_eq_left hp.out]
  show ((Formalism.GaloisCohomology.shaLen (GaloisStage.lData B.host p) (e : ℤ)).toNat : ℚ) = n
  rw [h, ENat.toNat_natCast]

end GlobalTheory.MemN
