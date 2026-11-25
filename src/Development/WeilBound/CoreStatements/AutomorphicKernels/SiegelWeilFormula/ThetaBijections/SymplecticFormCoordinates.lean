module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.SySmulRight
import Mathlib.Tactic.Linter.Style

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.TBij

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace Adp

variable (d : SD σ)

theorem om_ratV {κ : Type} [Fintype κ] (y z y' z' : κ → F) :
    om (ratV y z) (ratV y' z') = algebraMap F (AF F) (om (y, z) (y', z')) := by

  simp [om, ratV, dotProduct, map_sum, map_mul, map_sub]

end Adp

end PositivityTheory.SiegelWeilFormula.TBij
