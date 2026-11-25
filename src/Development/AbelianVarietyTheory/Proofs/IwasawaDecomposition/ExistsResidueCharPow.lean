module

public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Formalism.LocalRingCardinality.DataHost
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.PsiExist

section General

variable {L : Type} [Field L] [NumberField L]


theorem trivOn_pow {F : Type} [Field F] [NumberField F] [Algebra F L] {χ : HChar L} (h : χ.TrivOn F) (n : ℕ) :
    (χ ^ n).TrivOn F := by
  induction n with
  | zero => rw [pow_zero, ← mul_inv_cancel χ]; exact h.mul h.inv
  | succ n ih => rw [pow_succ]; exact ih.mul h


end General

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)



end GlobalTheory.Mem.PsiExist
