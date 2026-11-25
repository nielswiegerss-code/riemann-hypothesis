module

public import Formalism.PeriodIntegrals.JetsPhW
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InverseOmegaHolds
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.RingTheory.PowerSeries.Derivative

@[expose] public section

open Classical

namespace PI.JetsPhW.Inv

variable {p : ℕ} [Fact p.Prime]

theorem dX_eq_derivative (f : PowerSeries ℂ_[p]) : dX f = PowerSeries.derivative f := by
  ext n
  rw [PowerSeries.coeff_derivative, dX, PowerSeries.coeff_mk, mul_comm]

theorem inverse_omega_holds : InvOmega := by
  simpa only [InvOmega, IsIntP, IsWq, dX, flog, omegaW,
    UpperTheory.Reformulated.B.Gwa1.InvOmega, UpperTheory.Reformulated.B.Gwa1.IsIntP,
    UpperTheory.Reformulated.B.Gwa1.IsWq, UpperTheory.Reformulated.B.Gwa1.dX,
    UpperTheory.Reformulated.B.Gwa1.flog, UpperTheory.Reformulated.B.Gwa1.omegaW] using
    _root_.UpperTheory.Reformulated.B.Gwa1.inverse_omega_holds

end PI.JetsPhW.Inv
