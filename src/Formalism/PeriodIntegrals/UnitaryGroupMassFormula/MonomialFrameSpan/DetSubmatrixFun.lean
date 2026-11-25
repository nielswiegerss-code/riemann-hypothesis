module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.TypeStar
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCauchyBinet

@[expose] public section

open Matrix Finset

namespace GenFrameSpan

theorem det_mul_rect {R : Type*} [CommRing R] {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det = ∑ f : Fin k → Fin n, (∏ i, B (f i) i) * (A.submatrix id f).det := by
  apply _root_.GroundTheory.Heights₂.Heights.CauchyBinetAlt.det_mul_eq_sum <;> assumption

theorem det_submatrix_fun {R : Type*} [CommRing R] {p n : ℕ} (M : Matrix (Fin p) (Fin n) R)
    (f : Fin p → Fin n) :
    (M.submatrix id f).det = 0 ∨ ∃ (J : Fin p ↪o Fin n) (e : ℤ),
      (M.submatrix id f).det = (e : R) * (M.submatrix id J).det := by
  classical
  by_cases hf : Function.Injective f
  · right
    set s := Finset.univ.image f with hs
    have hcard : s.card = p := by
      rw [hs, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
    let J := s.orderEmbOfFin hcard
    have hmem : ∀ i, f i ∈ Set.range J := by
      intro i
      rw [Finset.range_orderEmbOfFin]
      simp [hs]
    choose g hg using hmem
    have hginj : Function.Injective g := by
      intro a b h
      apply hf
      rw [← hg a, ← hg b, h]
    let σ : Equiv.Perm (Fin p) := Equiv.ofBijective g (Finite.injective_iff_bijective.1 hginj)
    refine ⟨J, (Equiv.Perm.sign σ : ℤ), ?_⟩
    have e : M.submatrix id f = (M.submatrix id J).submatrix id σ := by
      ext a b
      simp [σ, hg]
    rw [e, Matrix.det_permute']
  · left
    rw [Function.Injective] at hf
    push Not at hf
    obtain ⟨i, j, hij, hne⟩ := hf
    exact Matrix.det_zero_of_column_eq hne (fun a => by simp [hij])

end GenFrameSpan
