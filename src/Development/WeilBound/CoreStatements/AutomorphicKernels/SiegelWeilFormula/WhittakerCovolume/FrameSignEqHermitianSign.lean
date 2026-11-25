module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ParabolicLowerBlockZero
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem rel_cA_incM {a b : Type} (X : Matrix a b E) : (incM F X).map (cA σ) = incM F (X.map σ) := by
  ext i j
  simp [incM, cA, inclR, Algebra.TensorProduct.map_tmul]

theorem rel_anti (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) : ∃ η : E, η ≠ 0 ∧ σ η = -η := by
  have hσ := _root_.GlobalTheory.AdelicU.cm_conj_conj h
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra hc
    push Not at hc
    have := h.2.1
    let w : InfinitePlace E := Classical.arbitrary _
    have hw : w.IsComplex := NumberField.IsTotallyComplex.isComplex w
    rw [NumberField.InfinitePlace.isComplex_iff] at hw
    apply hw
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext y
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq, ← Complex.star_def, ← h.2.2.2, hc]
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [map_sub, hσ, neg_sub]

end PositivityTheory.SiegelWeilFormula.KWhit
