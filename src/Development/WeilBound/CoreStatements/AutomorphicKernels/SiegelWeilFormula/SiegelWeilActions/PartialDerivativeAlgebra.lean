module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.BMat
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.SplitPrimeIdeals
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.LagrangianCondition
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.LagrangianConditionParabolicMul
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.RatVecCountable
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldB
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.IncMFromBlocks

@[expose] public section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C5 PositivityTheory.SiegelWeilFormula.Act.C4 PositivityTheory.SiegelWeilFormula.Act.C4.Bq

set_option linter.unusedSectionVars false

namespace PositivityTheory.SiegelWeilFormula.Act.C6

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} {L : LD d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}


theorem mul_eq_zero_of_supp {ι : Type} [Fintype ι] (P : ι → Prop) {M N : Matrix ι ι (AE F E)}
    (hM : ∀ r l, ¬ P l → M r l = 0) (hN : ∀ l c, P l → N l c = 0) : M * N = 0 := by
  ext r c
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : P l
  · rw [hN l c hl, mul_zero]
  · rw [hM r l hl, zero_mul]

theorem cA_inv' (hσ : ∀ x, σ (σ x) = x) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cA, hσ]
  | add a b ha hb => simp [map_add (f := _), ha, hb]

end PositivityTheory.SiegelWeilFormula.Act.C6
