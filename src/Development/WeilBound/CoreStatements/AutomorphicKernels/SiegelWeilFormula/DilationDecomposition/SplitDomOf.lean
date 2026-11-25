module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocDerBig
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.PiProdSch
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.ProdGenMem

@[expose] public section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Kdil

theorem isSw_gauss {m n : ℕ} {δ : ℝ} (hδ : 0 < δ) : IsSw (fun u : Fin m → Fin n → ℂ => (Real.exp (-δ * sq u) : ℂ)) := by
  obtain ⟨S, hS⟩ := KFock.fPSch (1 : PX m n) hδ
  refine ⟨S, funext fun u => ?_⟩
  rw [hS u]
  simp [evX, gs, sq, Complex.ofReal_exp, neg_mul]

end PositivityTheory.SiegelWeilFormula.Kdil
