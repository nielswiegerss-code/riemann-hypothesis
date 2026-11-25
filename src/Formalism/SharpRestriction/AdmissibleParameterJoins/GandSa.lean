module

public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero

@[expose] public section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.MainNotions.G
open scoped BigOperators

variable {D : D7} {L : SizeData₂ D}



theorem delta1_pos (s : Scale) : 0 < s.delta1 := by
  unfold Scale.delta1
  exact Real.rpow_pos_of_pos (by linarith [s.one_lt_alt]) _

theorem delta1_le_one (s : Scale) : s.delta1 ≤ 1 := by
  unfold Scale.delta1
  exact Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt s.one_lt_alt) (by linarith [s.eps_pos])

theorem frobenius_step_large_order {p : ℕ} (hp : IsResidueClassZero D p) : stepP D p = hP D p := by
  simp [stepP, IsSg, hp]

end Formalism.MainNotions.J
