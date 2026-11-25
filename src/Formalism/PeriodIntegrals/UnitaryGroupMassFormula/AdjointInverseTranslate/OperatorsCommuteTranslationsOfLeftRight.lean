module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.CoefLeftAAv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.AnaHpartUnique

@[expose] public section

open Matrix

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

theorem inUH_mul {n : ℕ} {H a b : Matrix (Fin n) (Fin n) ℂ} (ha : inUH H a) (hb : inUH H b) :
    inUH H (a * b) := by
  apply _root_.AAInvW.ana_mul <;> assumption

theorem operators_commute_translations_of_left_right (hL : LeftAA) (hR : RightAA) (hS : SsetUH) : OperatorsCommuteTranslations := by
  unfold OperatorsCommuteTranslations
  intro E _ _ k r z z' m hm u ell f _ _ hf s hs s' hs' g hg
  have hsg : inUH (Hpk k r) (s * g) := inUH_mul (hS k r z s hs) hg
  obtain ⟨hL1, hL2⟩ := hL E k r z m hm u ell (fun x => f (x * s')) s g hs hg
  obtain ⟨hR1, hR2⟩ := hR E k r z' m hm u ell f s' (s * g) hf hs' hsg
  exact ⟨hL1.trans hR1, hL2.trans hR2⟩

end AAInvW
