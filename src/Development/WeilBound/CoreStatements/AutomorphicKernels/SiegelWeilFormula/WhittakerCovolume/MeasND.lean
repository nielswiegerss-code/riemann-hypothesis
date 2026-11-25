module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.IsPureTIff
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.PlaneAd

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem meas_det_of_hasSig {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 :=
  _root_.PositivityTheory.Mix.det_ne_of_sig h

end PositivityTheory.SiegelWeilFormula.KWhit
