module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocNbar
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierTransformMatrixSpaceInvolution
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Decomp
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocForm
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocJJA
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.OppositeUnipotentWeylConj
import Mathlib.Tactic.Linter.Style

@[expose] public section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula

theorem jj_split {n : ℕ} (y : GR n) (hy : mR y = JJ n) :
    ∃ y₁ y₂ : GR n, mR y₁ = nU 1 ∧ mR y₂ = nbLoc (-1) ∧ y = y₁ * y₂ * y₁ := by
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 := Matrix.conjTranspose_one
  have h2 : (-1 : Matrix (Fin n) (Fin n) ℂ)ᴴ = -1 := by rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_one]
  let y₁ : GR n := Glob.DecH.mkGR (nU 1) (by rw [Glob.DecH.det_nU]; exact isUnit_one) (Glob.DecH.inG_nU h1)
  let y₂ : GR n := Glob.DecH.mkGR (Glob.nbar (-1)) (by rw [Glob.DecH.det_nbar]; exact isUnit_one) (Glob.DecH.inG_nbar h2)
  refine ⟨y₁, y₂, rfl, rfl, Subtype.ext (Units.ext ?_)⟩
  show mR y = mR y₁ * mR y₂ * mR y₁
  rw [hy]
  show JJ n = nU 1 * Glob.nbar (-1) * nU 1
  simp [JJ, nU, Glob.nbar, Matrix.fromBlocks_multiply]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end PositivityTheory.SiegelWeilFormula
