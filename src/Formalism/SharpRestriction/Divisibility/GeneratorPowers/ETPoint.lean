module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Tactic.ToDual
import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Lattice.Nat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage

@[expose] public section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Formalism.MainNotions.ModuliIntegralCharts ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

theorem etPoint_min {X : Type} [AddCommGroup X] (Q : X → ℤ) (hQ : ∀ a, 0 ≤ Q a) (y : X) (R' : ℕ) :
    ∃ z : X, ∀ z' : X, Q (y + R' • z) ≤ Q (y + R' • z') := by
  let S : Set ℕ := Set.range fun z : X => (Q (y + R' • z)).toNat
  have hS : S.Nonempty := ⟨_, 0, rfl⟩
  obtain ⟨z, hz⟩ := Nat.sInf_mem hS
  refine ⟨z, fun z' => ?_⟩
  have h1 : sInf S ≤ (Q (y + R' • z')).toNat := Nat.sInf_le ⟨z', rfl⟩
  have h2 := hQ (y + R' • z)
  have h3 := hQ (y + R' • z')
  have h4 : (Q (y + R' • z)).toNat = sInf S := hz
  omega

end Formalism.MainNotions.ModuliIntegralCharts.H1
