module

public import Formalism.FormalGroupLog.Statement
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Tactic.TypeStar

@[expose] public section

open MvPowerSeries

namespace Formalism.G.LogP

open Formalism.G.LogCR

variable {R : Type*} [CommRing R]

theorem hs2 {σ : Type*} {u v : MvPowerSeries σ R} (hu : constantCoeff u = 0)
    (hv : constantCoeff v = 0) : MvPowerSeries.HasSubst ![u, v] := by
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [hu, hv])

theorem hs3 {σ : Type*} {u v w : MvPowerSeries σ R} (hu : constantCoeff u = 0)
    (hv : constantCoeff v = 0) (hw : constantCoeff w = 0) : MvPowerSeries.HasSubst ![u, v, w] := by
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [hu, hv, hw])

theorem subst2_subst {σ τ : Type*} (Φ : MvPowerSeries (Fin 2) R) {u v : MvPowerSeries σ R}
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0) {b : σ → MvPowerSeries τ R}
    (hb : MvPowerSeries.HasSubst b) :
    (Φ.subst ![u, v]).subst b = Φ.subst ![u.subst b, v.subst b] := by
  rw [MvPowerSeries.subst_comp_subst_apply (hs2 hu hv) hb]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem psubst_subst {σ τ : Type*} (φ : PowerSeries R) {u : MvPowerSeries σ R}
    (hu : constantCoeff u = 0) {b : σ → MvPowerSeries τ R} (hb : MvPowerSeries.HasSubst b) :
    (φ.subst u).subst b = φ.subst (u.subst b) := by
  have hu' : MvPowerSeries.HasSubst (fun _ : Unit => u) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hu)
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply hu' hb]

theorem constantCoeff_subst_of_zero {σ τ : Type*} [Finite σ] [Finite τ]
    (Φ : MvPowerSeries σ R) {b : σ → MvPowerSeries τ R} (hb : ∀ i, constantCoeff (b i) = 0) :
    constantCoeff (Φ.subst b) = constantCoeff Φ := by
  have hb' : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
  rw [MvPowerSeries.constantCoeff_subst hb', finsum_eq_single _ 0]
  · simp
  · intro d hd
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra! h
      exact hd (Finsupp.ext h)
    have h0 : constantCoeff (d.prod fun s e => b s ^ e) = 0 := by
      rw [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hi)
      rw [map_pow, hb i, zero_pow hi]
    rw [h0, smul_zero]

variable (F : FormalGroup R)

theorem hb0 : MvPowerSeries.HasSubst ![(PowerSeries.X : PowerSeries R), 0] := by
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [PowerSeries.X])

end Formalism.G.LogP

namespace Formalism.G.LogP

open Formalism.G.LogCR

variable {R : Type*} [CommRing R]

theorem subst_zero' {σ τ : Type*} {b : σ → MvPowerSeries τ R} (hb : MvPowerSeries.HasSubst b) :
    (0 : MvPowerSeries σ R).subst b = 0 := by
  rw [← MvPowerSeries.coe_substAlgHom hb, map_zero]

theorem subst_XX (Φ : MvPowerSeries (Fin 2) R) :
    Φ.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1] = Φ := by
  have h : ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1] = MvPowerSeries.X := by
    funext i
    fin_cases i <;> rfl
  rw [h, MvPowerSeries.subst_self, id]

variable (F : FormalGroup R)

end Formalism.G.LogP

namespace Formalism.G.LogP

open Formalism.G.LogCR

variable {R : Type*} [CommRing R]

variable (F : FormalGroup R)

variable [Algebra ℚ R]

end Formalism.G.LogP

namespace Formalism.G.LogP

variable {R : Type*} [CommRing R]

theorem psubst_injective {f : PowerSeries R} (hf0 : PowerSeries.constantCoeff f = 0)
    (hf1 : PowerSeries.coeff 1 f = 1) {σ : Type*} {a b : MvPowerSeries σ R}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) (h : f.subst a = f.subst b) : a = b := by
  have : Invertible (PowerSeries.coeff 1 f) := hf1 ▸ invertibleOne
  have hfs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  have inv : ∀ c : MvPowerSeries σ R, constantCoeff c = 0 → f.substInv.subst (f.subst c) = c := by
    intro c hc
    have hcs : PowerSeries.HasSubst c := PowerSeries.HasSubst.of_constantCoeff_zero hc
    rw [← PowerSeries.subst_comp_subst_apply hfs hcs, PowerSeries.subst_substInv_left f hf0,
      PowerSeries.subst_X hcs]
  rw [← inv a ha, h, inv b hb]

end Formalism.G.LogP
