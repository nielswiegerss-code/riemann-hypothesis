module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HalfPrincipalAndSplit
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Mathlib.NumberTheory.RamificationInertia.Basic

@[expose] public section

set_option autoImplicit false

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit

open NumberField IsDedekindDomain UniqueFactorizationMonoid

theorem split_of_ncard {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (h : {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E) :
    (normalizedFactors (Ideal.span {((p : ℕ) : 𝓞 E)})).card = Module.finrank ℚ E ∧
      (normalizedFactors (Ideal.span {((p : ℕ) : 𝓞 E)})).Nodup := by
  apply GlobalTheory.HalfGen.factors_of_ncard_places <;> assumption


open Formalism.BasicNotions in
theorem g_splits (D : D7) (i : Fin 2) :
    (normalizedFactors (Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)})).card = Module.finrank ℚ D.host.E ∧
      (normalizedFactors (Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)})).Nodup :=
  split_of_ncard (D.host.g_prime i) (D.nd.g_split i)

end Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit
