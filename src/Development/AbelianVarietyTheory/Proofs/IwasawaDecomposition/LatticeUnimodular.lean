module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndepOfGqNeZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SubMemDifferentIdeal
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormSubEqOne
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
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoordinatesFlagVector
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GqPtOfNeZeroIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MulVecMemLatMap
public import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic

@[expose] public section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IntPair GlobalTheory.IntTerm Formalism.BasicNotions IsDedekindDomain
open Formalism.MainNotions.S (FlagG XS ddS FrameOK)
open Formalism.MainNotions.S.Lat (LFlag hS Tu gS XLam IsFixedConv FixedHyp)
open scoped nonZeroDivisors

namespace GlobalTheory.IntTerm.Conv

section Ideals

variable {E : Type} [Field E] [NumberField E]

theorem exists_local_gen {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) {P : Ideal (𝓞 E)} (hP : P ≠ ⊤) :
    ∃ c : E, c ≠ 0 ∧ c ∈ I ∧ ∀ x ∈ I, ∃ s : 𝓞 E, s ∉ P ∧ ∃ o : 𝓞 E, (s : E) * x = o * c := by
  have int {a b : E} (ha : a ∈ I) (hb : b ∈ I⁻¹) : ∃ o : 𝓞 E, (o : E) = a * b := by
    have := FractionalIdeal.mul_mem_mul ha hb
    rw [mul_inv_cancel₀ hI] at this
    exact (FractionalIdeal.mem_one_iff _).1 this
  obtain ⟨a, ha, b, hb, s, hs, e⟩ : ∃ a ∈ I, ∃ b ∈ I⁻¹, ∃ s : 𝓞 E, s ∉ P ∧ (s : E) = a * b := by
    by_contra h
    have h1 : (1 : E) ∈ I * I⁻¹ := by rw [mul_inv_cancel₀ hI]; exact FractionalIdeal.one_mem_one _
    obtain ⟨s, hs, e⟩ := FractionalIdeal.mul_induction_on (C := fun x => ∃ s ∈ P, (s : E) = x) h1
      (fun a ha b hb => by
        obtain ⟨o, e⟩ := int ha hb
        exact ⟨o, by_contra fun k => h ⟨a, ha, b, hb, o, k, e⟩, e⟩)
      (fun _ _ ⟨s, hs, e⟩ ⟨t, ht, f⟩ => ⟨s + t, add_mem hs ht, by rw [← e, ← f]; simp⟩)
    obtain rfl : s = 1 := RingOfIntegers.ext e
    exact hP ((Ideal.eq_top_iff_one _).2 hs)
  refine ⟨a, fun h => hs ?_, ha, fun x hx => ⟨s, hs, ?_⟩⟩
  · obtain rfl : s = 0 := RingOfIntegers.ext (by rw [e, h, zero_mul]; rfl)
    exact zero_mem _
  · obtain ⟨o, f⟩ := int hx hb
    exact ⟨o, by rw [e, f]; ring⟩

theorem exists_gen_dInv (j : ℕ) (P : Ideal (𝓞 E)) [hP : P.IsPrime] :
    ∃ c : E, c ≠ 0 ∧ c ∈ dInv E j ∧ (¬ P ∣ differentIdeal ℤ (𝓞 E) → c = 1) ∧
      ∀ x ∈ dInv E j, ∃ s : 𝓞 E, s ∉ P ∧ ∃ o : 𝓞 E, (s : E) * x = o * c := by
  by_cases h : P ∣ differentIdeal ℤ (𝓞 E)
  · obtain ⟨c, h1, h2, h3⟩ := exists_local_gen (I := dInv E j)
      (fun e => by simpa [e] using Iota.one_mem_dInv (E := E) j) hP.ne_top
    exact ⟨c, h1, h2, fun k => absurd h k, h3⟩
  · obtain ⟨s, hs, hn⟩ := SetLike.not_le_iff_exists.1 (mt Ideal.dvd_iff_le.2 h)
    refine ⟨1, one_ne_zero, Iota.one_mem_dInv j, fun _ => rfl, fun x hx =>
      ⟨s ^ j, fun k => hn (hP.mem_of_pow_mem j k), ?_⟩⟩
    have h0 : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot
    have := FractionalIdeal.mul_mem_mul
      (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 E)⁰ (P := E) (Ideal.pow_mem_pow hs j)) hx
    rw [FractionalIdeal.coeIdeal_pow, dInv, ← mul_pow, mul_inv_cancel₀ h0, one_pow] at this
    obtain ⟨o, e⟩ := (FractionalIdeal.mem_one_iff _).1 this
    exact ⟨o, by rw [mul_one]; exact e.symm⟩

theorem not_dvd_different {p : ℕ} (hp : p.Prime) (h : (placesOver E p).ncard = Module.finrank ℚ E)
    (P : Ideal (𝓞 E)) [hP : P.IsPrime] (hm : (p : 𝓞 E) ∈ P) : ¬ P ∣ differentIdeal ℤ (𝓞 E) := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp'.irreducible
  have e : HeightOneSpectrum.asIdeal '' placesOver E p = Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E) := by
    ext Q
    constructor
    · rintro ⟨v, hv, rfl⟩
      have := v.isPrime
      exact ⟨v.isPrime, (Ideal.liesOver_span_iff v.isPrime.ne_top hp').2 (by simpa [placesOver] using hv)⟩
    · rintro ⟨h1, h2⟩
      have k : (p : 𝓞 E) ∈ Q := by simpa using (Ideal.liesOver_span_iff h1.ne_top hp').1 h2
      exact ⟨⟨Q, h1, fun e => hp.ne_zero (by simpa [e] using k)⟩, k, rfl⟩
  have hd := GlobalTheory.SplitEmbSep.not_dvd_discr_of_split hp E (by
    rw [← e, Set.ncard_image_of_injective _ fun v w hvw => HeightOneSpectrum.ext hvw, h])
  exact not_dvd_differentIdeal_iff.2 ((not_dvd_discr_iff_forall_mem E (𝓞 E) hp').1 hd P hP (by simpa using hm))

end Ideals

section Record

variable (D : D7)

theorem ddS_eq : ddS D = (differentIdeal ℤ (𝓞 D.host.E) : Ideal (𝓞 D.host.E)) := by
  rw [ddS, differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 D.host.F) (𝓞 D.host.E),
    GlobalTheory.CMDiscrSq.differentIdeal_eq_top D.sp.cm, Ideal.top_mul]

theorem level_not_dvd (P : HeightOneSpectrum (𝓞 D.host.E)) (h : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    ¬ P.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.E) := by
  have := P.isPrime
  rw [gS, Nat.cast_mul] at h
  rcases P.isPrime.mem_or_mem h with h | h
  · exact not_dvd_different (D.host.g_prime 0) (D.nd.g_split 0) _ h
  · exact not_dvd_different (D.host.g_prime 1) (D.nd.g_split 1) _ h

variable {D}

end Record

end GlobalTheory.IntTerm.Conv
