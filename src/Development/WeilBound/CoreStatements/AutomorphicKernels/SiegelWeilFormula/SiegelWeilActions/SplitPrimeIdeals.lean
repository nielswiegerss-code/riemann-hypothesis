module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.ExistsGlCol
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldB
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose

@[expose] public section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

set_option linter.unusedSectionVars false

namespace PositivityTheory.SiegelWeilFormula.Act.C4

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ} (L : LD d)

theorem upper_block_mul_of_lower_zero {k : ℕ} {P Q : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) (AE F E)} (hQ : Q.toBlocks₂₁ = 0)
    (h : P * Q = 1) : P.toBlocks₁₁ * Q.toBlocks₁₁ = 1 := by
  have h1 := congrArg Matrix.toBlocks₁₁ h
  rw [← Matrix.fromBlocks_toBlocks P, ← Matrix.fromBlocks_toBlocks Q, Matrix.fromBlocks_multiply, hQ] at h1
  have h2 : (1 : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) (AE F E)).toBlocks₁₁ = 1 := by
    ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]
  simpa [h2] using h1

end PositivityTheory.SiegelWeilFormula.Act.C4
