module

import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.OrderedAtRanksOfPositionElement
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.BesselExistenceUniformOfFacts
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen

@[expose] public section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal ContDiff
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

open scoped Matrix.Norms.Elementwise

section Sm

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mat k r → (H →L[ℂ] H)}

theorem smooth_vectors_add {v1 v2 : H} (h1 : v1 ∈ smoothVecs (k := k) (r := r) σ)
    (h2 : v2 ∈ smoothVecs (k := k) (r := r) σ) : v1 + v2 ∈ smoothVecs (k := k) (r := r) σ := by
  intro g₀ hg₀
  obtain ⟨U1, F1, o1, m1, c1, e1⟩ := h1 g₀ hg₀
  obtain ⟨U2, F2, o2, m2, c2, e2⟩ := h2 g₀ hg₀
  refine ⟨U1 ∩ U2, fun g => F1 g + F2 g, o1.inter o2, ⟨m1, m2⟩,
    (c1.mono Set.inter_subset_left).add (c2.mono Set.inter_subset_right), fun g hg hgU => ?_⟩
  have a1 : σ g v1 = F1 g := e1 g hg.1 hgU
  have a2 : σ g v2 = F2 g := e2 g hg.2 hgU
  show σ g (v1 + v2) = F1 g + F2 g
  rw [map_add (f := _), a1, a2]

theorem smooth_vectors_smul (c : ℂ) {v : H} (h1 : v ∈ smoothVecs (k := k) (r := r) σ) :
    c • v ∈ smoothVecs (k := k) (r := r) σ := by
  intro g₀ hg₀
  obtain ⟨U1, F1, o1, m1, c1, e1⟩ := h1 g₀ hg₀
  refine ⟨U1, fun g => c • F1 g, o1, m1, c1.const_smul c, fun g hg hgU => ?_⟩
  have a1 : σ g v = F1 g := e1 g hg hgU
  show σ g (c • v) = c • F1 g
  rw [map_smul, a1]

theorem smooth_vectors_translate_unitary
    (hrep : ∀ a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ (a * b) = (σ a).comp (σ b))
    {v : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ) {a : Mat k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    σ a v ∈ smoothVecs (k := k) (r := r) σ := by
  apply _root_.Formalism.MainNotions.LeviCoordinates.smooth_vectors_translate <;> assumption

end Sm

namespace BData

variable (X : BData)

variable {X}

end BData

end Formalism.MainNotions.LeviCoordinates
