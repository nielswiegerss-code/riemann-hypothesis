module

public import Formalism.LocalRingCardinality.DataArith
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

namespace Formalism.MainNotions

open NumberField IsDedekindDomain Formalism.BasicNotions

theorem vAdd_pos_iff_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K}
    (ha : a ≠ 0) : 0 < vAdd la (a : K) ↔ a ∈ la.asIdeal := by
  have h0 : la.valuation K (a : K) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact_mod_cast ha
  have hle := la.valuation_le_one (K := K) a
  have hlt : la.valuation K (algebraMap (𝓞 K) K a) < 1 ↔ a ∈ la.asIdeal := la.valuation_lt_one_iff_mem a
  unfold vAdd
  constructor
  · intro h
    by_contra hm
    have h1 : la.valuation K (a : K) = 1 := le_antisymm hle (not_lt.1 fun h' => hm (hlt.1 h'))
    rw [h1] at h
    simp at h
  · intro hm
    have h2 : la.valuation K (a : K) < 1 := hlt.2 hm
    have h3 := (WithZero.log_lt_log h0 one_ne_zero).2 h2
    simp at h3
    omega

end Formalism.MainNotions
