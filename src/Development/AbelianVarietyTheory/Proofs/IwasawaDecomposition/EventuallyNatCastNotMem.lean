module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.RingTheory.DedekindDomain.Factorization
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.WeilDeligne NumberField IsDedekindDomain Polynomial

theorem eventually_natCast_notMem (E : Type) [Field E] [NumberField E] (l : ℕ) [hl : Fact l.Prime] :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal := by
  have h0 : (Ideal.span {((l : ℕ) : 𝓞 E)} : Ideal (𝓞 E)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hl.out.ne_zero
  rw [Filter.eventually_cofinite]
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  simpa [Ideal.dvd_span_singleton] using hw

end GlobalTheory.HeightCounting
