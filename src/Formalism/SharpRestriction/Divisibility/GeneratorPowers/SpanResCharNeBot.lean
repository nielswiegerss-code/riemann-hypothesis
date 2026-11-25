module

public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.LocalRingCardinality.DataArith
public import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal
import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj

namespace H1algLink

open Formalism.L2.Pj.Crude

variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))

theorem liesOver_resChar : la.asIdeal.LiesOver (Ideal.span {((resCharOf la : ℕ) : ℤ)}) := by
  have hl := resCharOf_prime la
  have hmax : (Ideal.span {((resCharOf la : ℕ) : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have hle : Ideal.span {((resCharOf la : ℕ) : ℤ)} ≤ la.asIdeal.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 K) ((resCharOf la : ℕ) : ℤ) ∈ la.asIdeal
    rw [map_natCast]
    exact crv_char_mem la
  have hne : la.asIdeal.under ℤ ≠ ⊤ := by
    intro h
    apply la.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : ℤ) ∈ la.asIdeal.under ℤ := by rw [h]; trivial
    change algebraMap ℤ (𝓞 K) 1 ∈ la.asIdeal at h1
    rwa [map_one] at h1
  exact ⟨hmax.eq_of_le hne hle⟩

theorem span_resChar_ne_bot : Ideal.span {((resCharOf la : ℕ) : ℤ)} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast (resCharOf_prime la).ne_zero

theorem eWL_eq : eWL K la = ramOverZ la := by
  have := liesOver_resChar la
  unfold eWL ramOverZ
  exact (Ideal.ramificationIdx'_eq_ramificationIdx _ _ (span_resChar_ne_bot la)).symm

theorem ramOverZ_ne_zero : ramOverZ la ≠ 0 := by
  have := liesOver_resChar la
  exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver la.asIdeal (span_resChar_ne_bot la)

theorem prime_mem_iff {p : ℕ} (hp : p.Prime) : ((p : ℕ) : 𝓞 K) ∈ la.asIdeal ↔ resCharOf la = p := by
  constructor
  · intro hm
    by_contra hne
    have hnd : ¬ resCharOf la ∣ p := fun hd => hne ((Nat.prime_dvd_prime_iff_eq (resCharOf_prime la) hp).1 hd)
    exact crv_not_mem la hnd hm
  · intro h
    rw [← h]
    exact crv_char_mem la

variable {D : D7}

end H1algLink


end Formalism.MainNotions.ModuliIntegralCharts.H1
