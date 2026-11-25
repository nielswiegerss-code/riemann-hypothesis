module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.ChiDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.ChiLocGal

section General

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]


open Pointwise in
theorem isFrob_conj {A : ValuationSubring Ω} {q : ℕ} {g σ : G E Ω} (hσ : IsFrob (F := E) (g • A) q σ) :
    IsFrob (F := E) A q (g⁻¹ * σ * g) := by
  have hm : ∀ x, g x ∈ g • A ↔ x ∈ A := fun x => ValuationSubring.smul_mem_pointwise_smul_iff
  refine ⟨?_, fun x hx => ?_⟩
  · have h1 : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h1, inv_smul_smul]
  · have h1 := hσ.2 (g x) (by rwa [ValuationSubring.valuation_le_one_iff, hm,
      ← ValuationSubring.valuation_le_one_iff])
    have e : σ (g x) - g x ^ q = g ((g⁻¹ * σ * g) x - x ^ q) := by
      rw [map_sub, map_pow, AlgEquiv.mul_apply, AlgEquiv.mul_apply, mul_inv_apply]
    rwa [e, valuation_lt_one_iff', ← map_inv₀, hm, hm, map_eq_zero_iff _ g.injective,
      ← valuation_lt_one_iff'] at h1

theorem frob_any [IsAlgClosure E Ω] {B : Type} [CommGroup B] {r r' : G E Ω →* B}
    {v : HeightOneSpectrum (𝓞 E)} {A₀ A : ValuationSubring Ω} (h0 : IsPlaceOver A₀ v) (hA : IsPlaceOver A v)
    (h : ∀ σ : G E Ω, IsFrob (F := E) A₀ (normV v) σ → r σ = r' σ) {σ : G E Ω}
    (hσ : IsFrob (F := E) A (normV v) σ) : r σ = r' σ := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver h0 hA
  have e : ∀ f : G E Ω →* B, f (g⁻¹ * σ * g) = f σ := fun f => by
    rw [map_mul, map_mul, map_inv, mul_comm (f g)⁻¹ (f σ), mul_assoc, inv_mul_cancel, mul_one]
  rw [← e r, ← e r']
  exact h _ (isFrob_conj hσ)

theorem locM_eq (P : HeightOneSpectrum (𝓞 E)) (x : (P.adicCompletion E)ˣ) :
    Units.map (Formalism.L2.NC.locM P) x = localIdele E P x := by
  rfl

end General

section Values

variable {E : Type} [Field E] [NumberField E]

theorem val_of_at {χ : HChar E} {ψ : Formalism.L2.NC.HC E} (h : ∀ x, ψ.χ x = χ.1 x) {P : HeightOneSpectrum (𝓞 E)} {α : ℂ}
    (hα : ψ.At P α) : ((χ.val P : ℂˣ) : ℂ) = α := by
  rw [← hα.2 _ (unif_spec P), h, locM_eq]
  rfl

theorem normV_eq_absNorm (P : HeightOneSpectrum (𝓞 E)) : normV P = Ideal.absNorm P.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

theorem val_block {μ η : HChar E} {r : ℕ} {P : HeightOneSpectrum (𝓞 E)} {α z : ℂ}
    (hα : (((μ * η⁻¹).val P : ℂˣ) : ℂ) = α) (hz : z = α⁻¹ * (Real.sqrt (normV P) : ℂ) ^ (-(r : ℤ))) :
    (((GlobalTheory.GalChar.block μ η r).val P : ℂˣ) : ℂ) = z⁻¹ := by
  rw [GlobalTheory.GalChar.block_val, hα, hz, mul_inv, inv_inv, zpow_neg, inv_inv, zpow_natCast, ← normV_eq_absNorm]
  congr 1
  have h0 : (0 : ℝ) ≤ (normV P : ℝ) := Nat.cast_nonneg _
  rw [show ((normV P : ℕ) : ℂ) = ((normV P : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow h0,
    Real.sqrt_eq_rpow, ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul h0]
  congr 2
  ring

end Values

end GlobalTheory.ChiLocGal
