module

public import Formalism.SharpRestriction.GrowthBounds.ObjPol
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.TypeStar
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees

@[expose] public section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section Arith

variable {p : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem natCast_unit_of_coprime (S : UniformizedDVR p O) {c : ℕ} (hc : Nat.Coprime c p) : IsUnit (c : O) := by
  by_contra h
  have hc' : (c : O) ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 h)
  have key : ((c.gcd p : ℕ) : ℤ) = (c : ℤ) * c.gcdA p + (p : ℤ) * c.gcdB p := Nat.gcd_eq_gcd_ab c p
  rw [Nat.Coprime.gcd_eq_one hc, Nat.cast_one] at key
  have key' : (1 : O) = (c : O) * ((c.gcdA p : ℤ) : O) + (p : O) * ((c.gcdB p : ℤ) : O) := by
    have := congrArg (Int.cast : ℤ → O) key
    push_cast at this
    exact this
  have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [key']
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hc') (Ideal.mul_mem_right _ _ S.p_mem)
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem dvr_charZero_of_prime (S : UniformizedDVR p O) (hp : p.Prime) : CharZero O := by
  refine charZero_of_inj_zero (fun n hn => ?_)
  by_contra hne
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hne p hp.ne_one
  rw [Nat.cast_mul, Nat.cast_pow] at hn
  have hpe : (p : O) ^ e ≠ 0 := pow_ne_zero _ S.p_ne
  have hm0 : (m : O) = 0 := (mul_eq_zero.1 hn).resolve_left hpe
  have hu := natCast_unit_of_coprime S ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm
  rw [hm0] at hu
  exact not_isUnit_zero hu

theorem dvr_fraction_field_charZero_prime (S : UniformizedDVR p O) (hp : p.Prime) : CharZero (KK O) := by
  haveI := dvr_charZero_of_prime S hp
  refine charZero_of_inj_zero (fun n hn => ?_)
  have h1 : algebraMap O (KK O) (n : O) = algebraMap O (KK O) 0 := by
    rw [map_natCast, map_zero]; exact hn
  have h2 : (n : O) = 0 := IsFractionRing.injective O (KK O) h1
  exact_mod_cast h2

end Arith

end Formalism.MainNotions.G.GLWeightTheory
