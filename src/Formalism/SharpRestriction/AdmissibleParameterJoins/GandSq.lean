module

public import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSo
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Mathlib.Tactic.Linter.Style
import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem

@[expose] public section

namespace Formalism.MainNotions.J

open MvPowerSeries Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

section G1

variable {p : ℕ} [Fact p.Prime] (g : G1 p) {σ τ : Type}

theorem cc_l : PowerSeries.constantCoeff g.l = 0 := by
  unfold G1.l
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Formalism.MainNotions.TaylorLogMetric.flog, PowerSeries.coeff_mk, ite_eq_left rfl]

theorem cc_lg {a : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0) : constantCoeff (g.lg a) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero ha g.l (cc_l g)

theorem cc_pt (hex : PowerSeries.constantCoeff g.ex = 0) {a : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0) :
    constantCoeff (g.pt a) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero ha g.ex hex

theorem lg_subst {c : σ → MvPowerSeries τ ℂ_[p]} (hc : HasSubst c) {a : MvPowerSeries σ ℂ_[p]}
    (ha : constantCoeff a = 0) : subst c (g.lg a) = g.lg (subst c a) :=
  J.subst_psubst hc ha g.l

theorem pt_subst {c : σ → MvPowerSeries τ ℂ_[p]} (hc : HasSubst c) {a : MvPowerSeries σ ℂ_[p]}
    (ha : constantCoeff a = 0) : subst c (g.pt a) = g.pt (subst c a) :=
  J.subst_psubst hc ha g.ex

theorem phAt_subst {c : σ → MvPowerSeries τ ℂ_[p]} (hc : HasSubst c) {a : MvPowerSeries σ ℂ_[p]}
    (ha : constantCoeff a = 0) : subst c (g.phAt a) = g.phAt (subst c a) :=
  J.subst_psubst hc ha g.ph

theorem add_subst (hex : PowerSeries.constantCoeff g.ex = 0) {c : σ → MvPowerSeries τ ℂ_[p]} (hc : HasSubst c)
    {a b : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    subst c (g.add a b) = g.add (subst c a) (subst c b) := by
  have h0 : constantCoeff (g.lg a + g.lg b) = 0 := by rw [map_add (f := _), cc_lg g ha, cc_lg g hb, add_zero]
  show subst c (g.pt (g.lg a + g.lg b)) = g.pt (g.lg (subst c a) + g.lg (subst c b))
  rw [pt_subst g hc h0, ← coe_substAlgHom hc, map_add (f := _), coe_substAlgHom, lg_subst g hc ha, lg_subst g hc hb]

theorem cc_add (hex : PowerSeries.constantCoeff g.ex = 0) {a b : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) : constantCoeff (g.add a b) = 0 :=
  cc_pt g hex (by rw [map_add (f := _), cc_lg g ha, cc_lg g hb, add_zero])

theorem be_subst (hex : PowerSeries.constantCoeff g.ex = 0) {c : σ → MvPowerSeries τ ℂ_[p]} (hc : HasSubst c)
    {a b : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    subst c (g.be a b) = g.be (subst c a) (subst c b) := by
  have hab := cc_add g hex ha hb
  show subst c (g.phAt (g.add a b) - g.phAt a - g.phAt b) =
    g.phAt (g.add (subst c a) (subst c b)) - g.phAt (subst c a) - g.phAt (subst c b)
  rw [← coe_substAlgHom hc, map_sub, map_sub, coe_substAlgHom, phAt_subst g hc hab, phAt_subst g hc ha,
    phAt_subst g hc hb, add_subst g hex hc ha hb]

theorem dg_Cmul (ep : ℂ_[p]) (i : σ) :
    (diagS (PowerSeries.C ep * g.l) i : MvPowerSeries σ ℂ_[p]) = C ep * g.lg (X i) := by
  have hX : PowerSeries.HasSubst (X i : MvPowerSeries σ ℂ_[p]) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_X i)
  unfold diagS G1.lg
  rw [← PowerSeries.smul_eq_C_mul, ← smul_eq_C_mul, ← PowerSeries.coe_substAlgHom hX, map_smul]

theorem cc_Cl (ep : ℂ_[p]) : PowerSeries.constantCoeff (PowerSeries.C ep * g.l) = 0 := by
  rw [map_mul, cc_l g, mul_zero]

end G1

end Formalism.MainNotions.J
