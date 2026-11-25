module

public import Formalism.RealPlaceAnalysis.StatementA
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CasimirCommutation

@[expose] public section

open scoped TensorProduct
open Finset

namespace Formalism.REAL

theorem casimir_central_holds : CasCentral := by
  intro A _ n ε E hE
  refine ⟨fun c d => ?_, fun c d h => _root_.UpperTheory.Reformulated.B.CasimirCommutation.casComm_casK_comm ε E hE c d h⟩
  have h := _root_.UpperTheory.Reformulated.B.CasimirCommutation.casComm_casK_comm (fun _ => true) E hE c d rfl
  have hC : CasK (fun _ : Fin n => true) E = Cas E := by simp [CasK, Cas]
  rwa [hC] at h

end Formalism.REAL
