module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSchwartzSums.SchwartzPolyGauss
import Mathlib.Tactic.Linter.Style

@[expose] public section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KMain

theorem holValueAt_finsum {ι : Type} (T : Finset ι) {f : ι → ℂ → ℂ} {c : ι → ℂ} {s₀ : ℂ}
    (h : ∀ i ∈ T, HolValueAt (f i) s₀ (c i)) : HolValueAt (fun s => ∑ i ∈ T, f i s) s₀ (∑ i ∈ T, c i) := by
  induction T using Finset.induction_on with
  | empty => simpa using holValueAt_const 0 s₀
  | insert a T ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem cosetSum_finsum {G : Type} [Group G] (Pp Γ : Subgroup G) {ι : Type} (T : Finset ι) (f : ι → G → ℂ) (g : G)
    (h : ∀ i ∈ T, GlobalTheory.Eis.CosetConv Pp Γ (f i) g) :
    GlobalTheory.Eis.cosetSum Pp Γ (fun x => ∑ i ∈ T, f i x) g = ∑ i ∈ T, GlobalTheory.Eis.cosetSum Pp Γ (f i) g := by
  unfold GlobalTheory.Eis.cosetSum GlobalTheory.Eis.term
  exact Summable.tsum_finsetSum fun i hi => (h i hi).of_norm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end PositivityTheory.SiegelWeilFormula.KMain
