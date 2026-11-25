module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
import Mathlib.Tactic.Linter.Style

@[expose] public section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KSing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem trace_inclR (e : E) :
    Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) e) = algebraMap F (AF F) (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange, Algebra.baseChange_lmul]
  rfl

theorem psi_rat {ψ : AddChar (AF F) ℂ} (hψ : ∀ x : F, ψ (algebraMap F (AF F) x) = 1) {n : ℕ}
    (X : Matrix (Fin n) (Fin n) E) : ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (incM F X)))) = 1 := by
  have e : Matrix.trace (incM F X) = inclR (F := F) (AF F) (Matrix.trace X) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.trace, incM, map_sum]
  rw [e, trace_inclR, ← map_neg, hψ]

end PositivityTheory.SiegelWeilFormula.KSing
