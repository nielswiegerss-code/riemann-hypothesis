module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.ExistsGlCol
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.IncMFromBlocks
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.MemRatVIff
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option linter.unusedSectionVars false

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp PositivityTheory.SiegelWeilFormula.kfour

namespace PositivityTheory.SiegelWeilFormula.Afc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

omit [NumberField E] in
theorem incM_mapc {p q : Type} (X : Matrix p q E) : (incM F X).map (cA σ) = incM F (X.map σ) := by
  ext i j; rfl

omit [NumberField E] in
theorem incM_tr {p q : Type} (X : Matrix p q E) : (incM F X)ᵀ = incM F Xᵀ := rfl

omit [NumberField E] in
theorem mapσ_mul' {p q r : Type} [Fintype q] (X : Matrix p q E) (Z : Matrix q r E) :
    (X * Z).map σ = X.map σ * Z.map σ :=
  Matrix.map_mul (f := (σ : E →+* E))

theorem nCond_rat {n : ℕ} {ε : ℤˣ} (T0 : Matrix (Fin n) (Fin n) E) (h : incM F T0 ∈ nCond σ n ε) (i j : Fin n) :
    T0 j i = -(((ε : ℤ) : E) * σ (T0 i j)) := by
  have h' : (incM F T0)ᵀ = -((((ε : ℤ) : AE F E)) • (incM F T0).map (cA σ)) := h
  have := congrFun (congrFun h' i) j
  simp only [Matrix.transpose_apply, incM, Matrix.map_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul] at this
  apply kfour.inclR_injective (F := F)
  rw [this, map_neg, map_mul, map_intCast]
  rw [kfour.cA_inclR' σ (T0 i j)]

end PositivityTheory.SiegelWeilFormula.Afc
