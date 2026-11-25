module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SplitPlaceTypes
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.Proof.ConjugatePlaces

open GlobalTheory.IndefiniteRowSideFullHecke

section Host

variable {R : Ranks} (H : Host R)

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  apply H.φ₀.injective
  have h1 := H.conjE_apply H.φ₀ (H.conj x)
  have h2 := H.conjE_apply H.φ₀ x
  refine h1.trans ?_
  show starRingEnd ℂ (H.φ₀ (H.conj x)) = _
  rw [h2, Complex.conj_conj]

theorem exists_conj_int (x : 𝓞 H.E) : ∃ y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) :=
  ⟨⟨H.conj (x : H.E), (x.isIntegral_coe).map (H.conj.toAlgHom.restrictScalars ℤ)⟩, rfl⟩

variable {H}

theorem isConjPl_symm {w w' : HeightOneSpectrum (𝓞 H.E)} (h : IsConjPl H w w') : IsConjPl H w' w :=
  fun x y hy => (h y x (by rw [hy, conj_conj])).symm

theorem isConjPl_unique {w w₁ w₂ : HeightOneSpectrum (𝓞 H.E)} (h₁ : IsConjPl H w w₁)
    (h₂ : IsConjPl H w w₂) : w₁ = w₂ := by
  ext y
  obtain ⟨x, hx⟩ := exists_conj_int H y
  have hy : (y : H.E) = H.conj (x : H.E) := by rw [hx, conj_conj]
  exact (h₁ x y hy).symm.trans (h₂ x y hy)

variable (H)

end Host

end GlobalTheory.Proof.ConjugatePlaces
