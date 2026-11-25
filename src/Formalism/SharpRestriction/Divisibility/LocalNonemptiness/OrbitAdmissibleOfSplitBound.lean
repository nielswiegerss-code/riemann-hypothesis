module

public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.MainNotions.DIV.Inh

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.OrbitPlaces

theorem even_add_order_two_le (D : D7) (h : HH D) (hev : Even (addOrderOf h)) : Even (addOrderOf h) ∧ 2 ≤ addOrderOf h := by
  have hfin : Finite (HH D) := Finite.of_fintype (Fin D.R.ord)
  refine ⟨hev, ?_⟩
  have hpos : 0 < addOrderOf h := addOrderOf_pos h
  obtain ⟨k, hk⟩ := hev
  omega

theorem orbOK_iff (D : D7) (p : ℕ) : OrbOK D p ↔ 5 ≤ p ∧ (IsSg D p ∨ HEv D p) := by
  constructor
  · rintro ⟨h5, hev, -⟩
    refine ⟨h5, ?_⟩
    by_cases hs : IsSg D p
    · exact Or.inl hs
    · right
      unfold nP at hev
      rw [ite_eq_right hs] at hev
      exact hev
  · rintro ⟨h5, hc⟩
    by_cases hs : IsSg D p
    · have hpos : 0 < addOrderOf (2 • hP D p) := by
        have hfin : Finite (HH D) := Finite.of_fintype (Fin D.R.ord)
        exact addOrderOf_pos _
      refine ⟨h5, ?_, ?_⟩
      · unfold nP
        rw [ite_eq_left hs]
        exact even_two_mul _
      · unfold nP
        rw [ite_eq_left hs]
        omega
    · have hev : HEv D p := hc.resolve_left hs
      obtain ⟨h1, h2⟩ := even_add_order_two_le D (hP D p) hev
      refine ⟨h5, ?_, ?_⟩
      · unfold nP
        rw [ite_eq_right hs]
        exact h1
      · unfold nP
        rw [ite_eq_right hs]
        exact h2

private theorem five_le_of_prime_not_small_not_split (D : D7) (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ D.host.splitBound)
    (hs : p ∉ D.host.toHostRaw.small) (hj : ¬ jacobiSym (-(D.host.d : ℤ)) p = 1) : 5 ≤ p := by
  by_contra hlt
  have h2 : 2 ≤ p := hp.two_le
  have hne2 : p ≠ 2 := by
    rintro rfl
    apply hs
    have hm : 2 ∈ D.host.toHostRaw.QS.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_trans (dvd_pow_self 2 (by omega)) D.host.tower_dvd,
        D.host.QS_pos.ne'⟩
    exact hm
  have hne4 : p ≠ 4 := by
    rintro rfl
    norm_num at hp
  obtain rfl : p = 3 := by omega
  exact hj (D.host.split_small 3 hp (by norm_num) h3)

theorem five_le_of_class (D : D7) (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ D.host.splitBound) (hc : IsResidueClassZero D p ∨ IsSg D p) : 5 ≤ p := by
  have hcls : D.host.cls p = PrimeClass.inertClass ∨ D.host.cls p = PrimeClass.signal := hc
  unfold Formalism.BasicNotions.Host.cls Formalism.BasicNotions.primeClass at hcls
  split_ifs at hcls with a1 a2 a3 a4 a5 <;>
    first
      | exact five_le_of_prime_not_small_not_split D p hp h3 a1 a4
      | simp at hcls

theorem orbOK_of_class (D : D7) (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ D.host.splitBound)
    (hc : (IsResidueClassZero D p ∧ HEv D p) ∨ IsSg D p) : OrbOK D p := (orbOK_iff D p).2 ⟨five_le_of_class D p hp h3 (hc.imp And.left id), hc.elim (fun h => Or.inr h.2) Or.inl⟩

theorem orbit_admissible_of_split_bound (D : D7) (h3 : 3 ≤ D.host.splitBound) : OrbitParityCond D := by
  unfold OrbitParityCond
  exact ⟨fun p hp hc => orbOK_of_class D p hp h3 hc, fun p hp hc => five_le_of_class D p hp h3 (Or.inl hc)⟩

end Formalism.MainNotions.DIV.Inh
