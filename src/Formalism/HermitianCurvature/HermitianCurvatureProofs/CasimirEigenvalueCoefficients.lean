module

public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
import Mathlib.Tactic.TypeStar

@[expose] public section

open Matrix Finset Filter Topology
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.B

namespace Qb1

variable {k r : ℕ} {Vs : Type} [NormedAddCommGroup Vs] [NormedSpace ℂ Vs]

theorem ckOn_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {f f' : Mx k r → E}
    (he : ∀ g ∈ GV k r, f g = f' g) (h : CkOn m (GV k r) f) : CkOn m (GV k r) f' := by
  intro g₀ hg₀
  obtain ⟨U, F, a, b, c, d⟩ := h g₀ hg₀
  exact ⟨U, F, a, b, c, fun g hg hgG => (he g hgG).symm.trans (d g hg hgG)⟩

variable {σ : Mx k r → (Vs →L[ℂ] Vs)}

theorem lie1 (Z : Mx k r) : inLie k r (hpart1 (Hpk k r) Z) := Qx2.hpart1_lie Z

theorem lie2 (Z : Mx k r) : inLie k r (hpart2 (Hpk k r) Z) := Qx2.hpart2_lie Z

end Qb1

end Formalism.FourierDecayAlt.P
