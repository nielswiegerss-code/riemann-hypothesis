module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.Imports
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.SigmaSigma
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.DecAlg
import Development.WeilBound.ThetaLifts.LatticeBasics.ConstIdele

@[expose] public section

open scoped TensorProduct Matrix
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.KAway

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem smul_toBlocks₁₁ {n : ℕ} (e : AF F) (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :
    (e • X).toBlocks₁₁ = e • X.toBlocks₁₁ := rfl
theorem smul_toBlocks₁₂ {n : ℕ} (e : AF F) (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :
    (e • X).toBlocks₁₂ = e • X.toBlocks₁₂ := rfl
theorem smul_toBlocks₂₁ {n : ℕ} (e : AF F) (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :
    (e • X).toBlocks₂₁ = e • X.toBlocks₂₁ := rfl
theorem smul_toBlocks₂₂ {n : ℕ} (e : AF F) (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :
    (e • X).toBlocks₂₂ = e • X.toBlocks₂₂ := rfl

theorem one_toBlocks₁₁ {n : ℕ} : (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).toBlocks₁₁ = 1 := by
  ext i j; simp [toBlocks₁₁, Matrix.one_apply]
theorem one_toBlocks₁₂ {n : ℕ} : (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).toBlocks₁₂ = 0 := by
  ext i j; simp [toBlocks₁₂]
theorem one_toBlocks₂₁ {n : ℕ} : (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).toBlocks₂₁ = 0 := by
  ext i j; simp [toBlocks₂₁]
theorem one_toBlocks₂₂ {n : ℕ} : (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).toBlocks₂₂ = 1 := by
  ext i j; simp [toBlocks₂₂, Matrix.one_apply]

end PositivityTheory.SiegelWeilFormula.KAway
