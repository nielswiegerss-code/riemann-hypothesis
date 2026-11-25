module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import ReciprocityTheory.DualLattices.TensorSpan
public import ReciprocityTheory.DualLattices.ValuationDetEqOfSpanEq
public import ReciprocityTheory.DualLattices.ValuationFourierLeOne
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import ReciprocityTheory.DualLattices.CotangentSurjective

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Ra

theorem charmem : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ ψ : AddChar N C, (fun x => ψ x) ∈ AA.carrier := by
  intro p _ C _ _ _ v R _ _ hv _ N _ _ _ AA ψ
  obtain ⟨B, hB, hAA⟩ := AA.lat
  rw [hAA, ← dualLat_dualLat_spanCols B hB, ← hAA]
  intro u hu
  obtain ⟨r, hr⟩ := hv.exists_of_le_one
    (valuation_fourier_le_one v hv (fun _ : Unit => ψ) AA hu ())
  refine ⟨r, hr.trans ?_⟩
  rw [fourier_apply']
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

end PositivityTheory.HtPt.Ra
