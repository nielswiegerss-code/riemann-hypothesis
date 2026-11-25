module

public import Formalism.GradedWeylDivisibility.StatementA
import Mathlib.Tactic.TypeStar
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowdivLemmas

@[expose] public section

open MvPolynomial

namespace Formalism.GradedWeylDivisibility

theorem weylModuleRowDividedPowerStable : WeylRowDivStable := by
  unfold WeylRowDivStable
  intro R _ r n hn ν a b k f hf
  let L : MvPolynomial (Fin r × Fin n) R →ₗ[R] MvPolynomial (Fin r × Fin n) R :=
    { toFun := rowDiv R a b k
      map_add' := _root_.Formalism.GradedWeylDivisibility.rowDiv_add R a b k
      map_smul' := _root_.Formalism.GradedWeylDivisibility.rowDiv_smul R a b k }
  have key : weyl R r n hn ν ≤ (weyl R r n hn ν).comap L := by
    unfold weyl
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    exact Submodule.subset_span ⟨(a, b, k) :: w, rfl⟩
  exact key hf

end Formalism.GradedWeylDivisibility
