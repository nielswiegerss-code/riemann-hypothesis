module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases

@[expose] public section

namespace GlobalTheory.TripleGal.HodgeOfAtt

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

theorem not_mem_placesOver_of_ne {D : D7} {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (v : HeightOneSpectrum (𝓞 D.host.E)) (h1 : v ∈ placesOver D.host.E p) : v ∉ placesOver D.host.E q := fun h2 => by
  have hc : IsCoprime (p : 𝓞 D.host.E) (q : 𝓞 D.host.E) := ((Nat.coprime_primes hp hq).mpr hne).cast
  obtain ⟨a, b, hab⟩ := hc
  refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
  exact hab ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left a h1) (v.asIdeal.mul_mem_left b h2)

theorem not_mem_pD (D : D7) (i : D.ntw.Tw) {v : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : v ∈ placesOver D.host.E (D.ntw.l i)) : v ∉ D.ntw.pD i := by
  intro hp
  have hv' : v ∈ placesOver D.host.E (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← D.ntw.pD_eq i]; exact hp
  have hl : (D.ntw.l i).Prime := (D.ntw.lPrime i).out
  split_ifs at hv' with h
  · exact not_mem_placesOver_of_ne D.host.pde'_prime hl (h ▸ D.host.pde_ne.symm) v hv' hv
  · exact not_mem_placesOver_of_ne D.host.pde_prime hl (Ne.symm h) v hv' hv

end GlobalTheory.TripleGal.HodgeOfAtt
