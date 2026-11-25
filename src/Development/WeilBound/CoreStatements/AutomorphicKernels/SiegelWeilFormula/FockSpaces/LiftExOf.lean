module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.ProdGenMem

@[expose] public section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFock

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem fP_add {m n : ℕ} (P Q : PX m n) : fP (P + Q) = fP P + fP Q := by
  funext u
  simp only [fP, evX, map_add (f := _), Pi.add_apply, add_mul]

theorem fP_smul {m n : ℕ} (a : ℂ) (P : PX m n) : fP (a • P) = a • fP P := by
  funext u
  simp only [fP, evX, MvPolynomial.smul_eval, Pi.smul_apply, smul_eq_mul, mul_assoc]

end PositivityTheory.SiegelWeilFormula.KFock
