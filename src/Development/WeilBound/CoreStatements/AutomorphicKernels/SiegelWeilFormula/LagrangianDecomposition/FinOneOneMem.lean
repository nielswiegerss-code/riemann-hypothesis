module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.BlockIndexInrLast
import Mathlib.Tactic.Linter.Style

@[expose] public section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem finOne_one_mem : finOne F • (1 : AE F E) ∈ intHat F E := by
  refine AddSubgroup.subset_closure ⟨finOne F, ?_, fun v => ?_, 1, ?_⟩
  · show InfiniteAdeleRing.ringEquiv_mixedSpace F (finOne F).1 = 0
    rw [show (finOne F).1 = 0 from rfl, map_zero]
  · rw [show evFin F v (finOne F) = 1 from map_one (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)]
    exact one_mem _
  · simp

theorem int_blk {N n : ℕ} (h : n + 1 = N) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :
    (∀ u v, finOne F • blk h M 1 u v ∈ intHat F E) ↔ ∀ u v, finOne F • M u v ∈ intHat F E := by
  constructor
  · intro H u v
    have := H (Sum.map (em0 h) (em0 h) u) (Sum.map (em0 h) (em0 h) v)
    rwa [blk_map_apply] at this
  · intro H u v
    rw [blk_apply]
    generalize eB h u = x
    generalize eB h v = y
    rcases x with x | x <;> rcases y with y | y
    · exact H x y
    · simp
    · simp
    · simp only [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
      split_ifs
      · exact finOne_one_mem
      · simp

end PositivityTheory.SiegelWeilFormula.Ald
