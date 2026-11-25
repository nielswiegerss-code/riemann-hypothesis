module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.FockLatticeInjective
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.PiProdSch

@[expose] public section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFock

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isSw_fP {m n : ℕ} (P : PX m n) : IsSw (fP P) := by
  obtain ⟨S, hS⟩ := fPSch P (c := 2 * Real.pi) (by positivity)
  exact ⟨S, funext fun x => by rw [hS]; rfl⟩

end PositivityTheory.SiegelWeilFormula.KFock
