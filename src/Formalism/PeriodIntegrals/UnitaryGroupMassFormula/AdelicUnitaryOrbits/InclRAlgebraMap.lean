module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.Tactic.Lemma

@[expose] public section

namespace PIW.AdelicOrbitU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [Field E] [Algebra F E]

lemma sigR_inclR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (e : E) :
    sigR R σ (inclR R e) = inclR R (σ e) :=
  DFunLike.congr_fun (Algebra.TensorProduct.map_comp_includeRight (AlgHom.id F R) σ) e

lemma isHerm_JR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) :
    Formalism.UG.IsHerm (sigR R σ) (JR R J) := by
  unfold Formalism.UG.IsHerm Formalism.UG.cT
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, JR, sigR_inclR, hJ]

lemma isUnit_det_JR (R : Type) [CommRing R] [Algebra F R] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : J.det ≠ 0) : IsUnit (JR (F := F) R J).det := by
  have h : (JR (F := F) R J).det = inclR (F := F) R J.det := by
    rw [RingHom.map_det]; rfl
  rw [h]
  exact (isUnit_iff_ne_zero.mpr hJ).map _

lemma inclR_algebraMap (R : Type) [CommRing R] [Algebra F R] (b : F) :
    inclR R (algebraMap F E b) = algebraMap F (R ⊗[F] E) b :=
  (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes b

end SlopeTestRemainingChoices

end PIW.AdelicOrbitU
