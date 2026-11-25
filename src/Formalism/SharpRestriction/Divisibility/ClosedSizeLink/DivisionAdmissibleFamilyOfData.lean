module

public import Formalism.SharpRestriction.ElevenLe
import Formalism.LocalRingCardinality.DataAmbForm
public import Formalism.SharpRestriction.ParConsts

@[expose] public section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions Formalism.BasicNotions.DV

section One

variable {D : D7} (L : SizeData₂ D)

theorem prod_gTypes : (∏ g ∈ L.gTypes, (g : ℝ)) = (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) := by
  simpa [SizeData₂.gTypes] using Finset.prod_pair D.host.g_ne

theorem x_pos : 0 < L.sc.x := lt_trans zero_lt_one L.sc.one_lt_alt

theorem one_le_b : 1 ≤ L.sc.b := by
  unfold Scale.b
  exact Real.one_le_exp (by unfold Scale.L; exact Real.rpow_nonneg (x_pos L).le _)

theorem one_le_a : 1 ≤ L.sc.a := by
  unfold Scale.a
  nlinarith [L.sc.one_lt_alt.le, one_le_b L]

theorem La_nonneg (hS : SizeQD L) : 0 ≤ L.La := by
  unfold SizeData₂.La
  exact Real.log_nonneg (by nlinarith [one_le_a L, hS.2.2.2.2.2.2.1])

end One

end Formalism.MainNotions.DIV
