module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.GoodAwayEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.ProdGenMem

@[expose] public section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFock

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem fP_one_ne {m n : ℕ} (u : Fin m → Fin n → ℂ) : fP (1 : PX m n) u ≠ 0 := by
  unfold fP evX gs
  rw [map_one, one_mul]
  exact Complex.exp_ne_zero _

end PositivityTheory.SiegelWeilFormula.KFock
