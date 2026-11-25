module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.LinearFormAdelic
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.BMat
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.SplitPrimeIdeals
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.DoubledGroupTopologicalProperties
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.RatVecCountable
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MemStabiliserIffFrameLowerBlock
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act.C5.Meas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} (L : LD d)

theorem eps_sq {R : Type} [Ring R] (ε : ℤˣ) : ((ε : ℤ) : R) * ((ε : ℤ) : R) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

theorem inclR_smul' (f : F) (e : E) :
    inclR (F := F) (AF F) (f • e) = algebraMap F (AF F) f • inclR (F := F) (AF F) e := by
  rw [inclR_eq', inclR_eq', TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul,
    mul_one, Algebra.algebraMap_eq_smul_one]

end PositivityTheory.SiegelWeilFormula.Act.C5.Meas
