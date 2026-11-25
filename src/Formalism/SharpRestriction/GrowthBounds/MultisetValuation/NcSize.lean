module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.StmtNumEOf
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcIotaInj
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcLgpLe
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcTsumOdd

@[expose] public section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

theorem nc_a_ge : (1 : ℝ) ≤ L.sc.a := by
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have hL : 0 ≤ L.sc.L := by
    simp only [Formalism.BasicNotions.Scale.L]
    exact Real.rpow_nonneg (by linarith) _
  have hb : 1 ≤ L.sc.b := by
    simp only [Formalism.BasicNotions.Scale.b]
    exact Real.one_le_exp hL
  simp only [Formalism.BasicNotions.Scale.a]
  exact one_le_mul_of_one_le_of_one_le hx.le hb

end Formalism.MainNotions.FormalGroupSystem.Pf
