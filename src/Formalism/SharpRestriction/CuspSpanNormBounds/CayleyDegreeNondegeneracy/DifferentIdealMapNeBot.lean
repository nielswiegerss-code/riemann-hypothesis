module

import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemInvCoeIdeal
public import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
public import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Tactic.TypeStar
import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
import Formalism.SharpRestriction.CuspSpanNormBounds.JExistsNatSmulMemL

@[expose] public section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals
open scoped nonZeroDivisors

section Fr

variable (D : D7)

theorem basis_vector_mem_span {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (a : Fin D.R.rS) : F0.e a ∈ XS D F0 := by
  apply _root_.Formalism.L2.SG.Pf.Cnt.R3.e_mem_XS <;> assumption

end Fr

end Formalism.MainNotions.BridgeLemma₂
