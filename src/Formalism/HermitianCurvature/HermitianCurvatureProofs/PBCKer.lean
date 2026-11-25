module

public import Formalism.HermitianCurvature.StatementTB
import Mathlib.NumberTheory.Height.NumberField

@[expose] public section

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder

open Classical

theorem psd_herm {Z : Type} (P : Finset Z) (K : Z → Z → ℂ) (hK : TB.PSDOn P K) {p q : Z} (hp : p ∈ P)
    (hq : q ∈ P) : K q p = conj (K p q) := by
  have h := hK.1.apply ⟨p, hp⟩ ⟨q, hq⟩
  simp only [Matrix.of_apply] at h
  rw [← h]
  simp

theorem psd_diag {Z : Type} (P : Finset Z) (K : Z → Z → ℂ) (hK : TB.PSDOn P K) {p : Z} (hp : p ∈ P) :
    0 ≤ K p p := by
  have h := hK.diag_nonneg (i := ⟨p, hp⟩)
  simpa [Matrix.of_apply] using h

end Formalism.FourierDecayAlt.P.PBC
