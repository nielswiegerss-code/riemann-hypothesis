module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.GoodAwayEx

@[expose] public section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace RD

variable {d : SD σ} (R : RD d) {w : InfinitePlace F}
  {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}

theorem isSw_lin {m n : ℕ} {f g : (Fin m → Fin n → ℂ) → ℂ} (a : ℂ) (hf : IsSw f) (hg : IsSw g) : IsSw (a • f + g) := by
  obtain ⟨φ, hφ⟩ := hf
  obtain ⟨φ', hφ'⟩ := hg
  exact ⟨a • φ + φ', by funext u; simp [← hφ, ← hφ']⟩

end RD

end PositivityTheory.SiegelWeilFormula
