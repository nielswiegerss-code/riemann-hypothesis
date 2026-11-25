module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DZTranspose
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.WeylCubeConjUnipotent
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.RDIota
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.OppositeUnipotentWeylConj

@[expose] public section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem eps_of_unit {n : ℕ} (hn : 1 ≤ n) (ε ε' : ℤˣ)
    (h : (wM n ((ε : ℤ) : ℂ))ᵀ * Krd.Qc n ε' * (wM n ((ε : ℤ) : ℂ)).map star = Krd.Qc n ε') : ε = ε' := by
  have h2 := congrArg Matrix.toBlocks₂₁ h
  simp [wM, Krd.Qc, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply] at h2
  have h3 := congrFun (congrFun h2 ⟨0, hn⟩) ⟨0, hn⟩
  simp at h3
  exact Units.ext (by exact_mod_cast h3)

end PositivityTheory.SiegelWeilFormula
