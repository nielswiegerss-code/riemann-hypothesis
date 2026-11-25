module

public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic.TypeStar

@[expose] public section

open scoped BigOperators
open Classical

namespace PI.OrbJet.AO

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime]
variable {σ τ υ : Type*}

theorem rename_subst' (e : σ ↪ τ) {a : υ → MvPowerSeries σ ℂ_[p]} (ha : HasSubst a)
    (f : MvPowerSeries υ ℂ_[p]) :
    rename e (subst a f) = subst (fun s => rename e (a s)) f := by
  rw [rename_eq_subst, subst_comp_subst_apply ha (HasSubst.X_comp e)]
  simp only [rename_eq_subst]

theorem subst_rename' (e : σ ↪ τ) {b : τ → MvPowerSeries υ ℂ_[p]} (hb : HasSubst b)
    (f : MvPowerSeries σ ℂ_[p]) :
    subst b (rename e f) = subst (fun w => b (e w)) f := by
  rw [rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp e) hb]
  simp only [Function.comp_apply, subst_X hb]

theorem rename_psubst (e : σ ↪ τ) {g : MvPowerSeries σ ℂ_[p]} (hg : PowerSeries.HasSubst g)
    (f : PowerSeries ℂ_[p]) :
    rename e (PowerSeries.subst g f) = PowerSeries.subst (rename e g) f := by
  rw [PowerSeries.subst, rename_subst' e hg.const]
  rfl

end PI.OrbJet.AO
