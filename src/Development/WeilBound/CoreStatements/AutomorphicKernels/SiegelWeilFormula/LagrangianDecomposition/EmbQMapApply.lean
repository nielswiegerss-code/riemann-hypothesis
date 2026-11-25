module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ChartA
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ChartB
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.UnitaryConjIff
import Mathlib.Tactic.Linter.Style

@[expose] public section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem embQ_mul_left {m n N : ℕ} (h : n + 1 = N) (L : Matrix (Fin m) (Fin m) (AE F E))
    (Q : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) : L * embQ h Q = embQ h (L * Q) := by
  ext a c
  simp only [embQ, Matrix.mul_apply, Matrix.submatrix_apply, id]
  rcases eB h c with x | x <;> simp [Matrix.mul_apply]

theorem embQ_map_apply {R : Type*} [Zero R] {m n N : ℕ} (h : n + 1 = N) (Q : Matrix (Fin m) (Fin n ⊕ Fin n) R)
    (a : Fin m) (v : Fin n ⊕ Fin n) : embQ h Q a (Sum.map (em0 h) (em0 h) v) = Q a v := by
  simp [embQ, eB_map]

theorem frQ_left {m k : ℕ} (c : GL (Fin k ⊕ Fin k) E) (L : Matrix (Fin m) (Fin m) (AE F E))
    (w : Matrix (Fin m) (Fin k ⊕ Fin k) (AE F E)) : frQ c (L * w) = L * frQ c w := by
  rw [frQ, frQ, Matrix.mul_assoc]

end PositivityTheory.SiegelWeilFormula.Ald
