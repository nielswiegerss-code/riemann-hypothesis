module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
import Mathlib.Tactic.Linter.Style

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem lin_addChar_sum {A : Type} [AddCommMonoid A] (ψ : AddChar A ℂ) {ι : Type} (s : Finset ι) (f : ι → A) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) :=
  map_prod ψ.toMonoidHom (fun i => Multiplicative.ofAdd (f i)) s

theorem lin_holValueAt_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (h : ι → ℂ → ℂ) (v : ι → ℂ) (s₀ : ℂ)
    (hh : ∀ i ∈ s, HolValueAt (h i) s₀ (v i)) :
    HolValueAt (fun z => ∑ i ∈ s, c i * h i z) s₀ (∑ i ∈ s, c i * v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using holValueAt_const 0 s₀
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact ((holValueAt_const (c j) s₀).mul (hh j (Finset.mem_insert_self j s))).add
      (ih fun i hi => hh i (Finset.mem_insert_of_mem hi))

end PositivityTheory.SiegelWeilFormula.KWhit
