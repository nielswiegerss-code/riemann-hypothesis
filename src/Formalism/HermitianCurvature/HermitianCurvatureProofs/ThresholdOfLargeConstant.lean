module

public import Formalism.HermitianCurvature.StatementJF
import Formalism.HermitianCurvature.BigCellVanishingOfCommute

@[expose] public section

open Matrix MeasureTheory

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

theorem xi_eq_xiTau_one_one {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (p : B.SS k r) :
    JF.xiP D p = B.xiTau D (1, 1) p := by
  have hs : ∀ x : ℝ, star (Complex.exp (Complex.I * (x : ℂ))) = Complex.exp (-(Complex.I * (x : ℂ))) := by
    intro x
    show (starRingEnd ℂ) (Complex.exp (Complex.I * (x : ℂ))) = _
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]
  simp only [JF.xiP, B.xiTau, psi, B.lam, hs]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end Formalism.FourierDecayAlt.P
