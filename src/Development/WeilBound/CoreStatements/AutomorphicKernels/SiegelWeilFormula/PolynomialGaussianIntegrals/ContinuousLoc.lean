module

public import GroundTheory.GlobalFields.Adele.IntegersLattice
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.FockLatticeInjective
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.IntSch
import Mathlib.Tactic.Linter.Style

@[expose] public section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFPB


variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

theorem homeo_symm_eq (x : mixedEmbedding.mixedSpace F) :
    (GroundTheory.Global.homeomorphMixedSpace F).symm x = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x := by
  apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
  rw [RingEquiv.apply_symm_apply]
  exact (GroundTheory.Global.homeomorphMixedSpace F).apply_symm_apply x

end PositivityTheory.SiegelWeilFormula.KFPB
