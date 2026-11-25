module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzLinearChange
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.RDIota
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.MatrixRepMul
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.OppositeUnipotentWeylConj
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.StepNB
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.StepNC
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DZTranspose
import Mathlib.Tactic.Linter.Style

@[expose] public section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem dZ_conj_diag {n : ℕ} {ζ : ℂ} (h : ζ ≠ 0) (A D : Matrix (Fin n) (Fin n) ℂ) :
    dZ n ζ⁻¹ * Matrix.fromBlocks A 0 0 D * dZ n ζ = Matrix.fromBlocks A 0 0 D := by
  simp [dZ, Matrix.fromBlocks_multiply, smul_smul, mul_inv_cancel₀ h]

theorem mapStar_mulR {p q r : Type} [Fintype q] (A : Matrix p q ℂ) (B : Matrix q r ℂ) :
    (A * B).map star = A.map star * B.map star := by
  ext i j
  simp [Matrix.mul_apply, Matrix.map_apply]

namespace RD

variable {d : SD σ} (R : RD d) (w : InfinitePlace F)

theorem absE_ne (x : (AE F E)ˣ) : (absE F E x : ℝ) ≠ 0 := by
  intro h
  have h1 : absE F E x * absE F E x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have h0 : absE F E x = 0 := by exact_mod_cast h
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

end RD

end PositivityTheory.SiegelWeilFormula
