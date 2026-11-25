module

public import Formalism.SatakeDualWeyl.Statement

@[expose] public section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

section Gen

variable {A R : Type} [CommRing A] [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem levelvsplit_coe_bc (f : R →+* A) (u : GL n R) :
    ((bc (n := n) f u : GL n A) : Matrix n n A) = (u : Matrix n n R).map f := by
  rfl

theorem levelvsplit_mem_range_iff (f : R →+* A) (hf : Function.Injective f) (g : GL n A) :
    g ∈ (bc (n := n) f).range ↔
      (∀ i j, (g : Matrix n n A) i j ∈ Set.range f) ∧
        ∀ i j, ((g⁻¹ : GL n A) : Matrix n n A) i j ∈ Set.range f := by
  constructor
  · intro hg
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hg
    refine ⟨fun i j => ⟨(u : Matrix n n R) i j, rfl⟩, fun i j => ⟨((u⁻¹ : GL n R) : Matrix n n R) i j, ?_⟩⟩
    rw [← map_inv (bc (n := n) f) u]
    rfl
  · rintro ⟨h1, h2⟩
    choose M hM using h1
    choose N hN using h2
    have hinj : Function.Injective (f.mapMatrix : Matrix n n R →+* Matrix n n A) :=
      Matrix.map_injective hf
    have hMg : f.mapMatrix (Matrix.of M) = (g : Matrix n n A) := by
      ext i j
      exact hM i j
    have hNg : f.mapMatrix (Matrix.of N) = ((g⁻¹ : GL n A) : Matrix n n A) := by
      ext i j
      exact hN i j
    have e1 : Matrix.of M * Matrix.of N = 1 := hinj (by rw [map_mul, map_one, hMg, hNg, Units.mul_inv])
    have e2 : Matrix.of N * Matrix.of M = 1 := hinj (by rw [map_mul, map_one, hMg, hNg, Units.inv_mul])
    exact MonoidHom.mem_range.mpr ⟨⟨Matrix.of M, Matrix.of N, e1, e2⟩, Units.ext hMg⟩

end Gen

section Split

variable {B K : Type} [CommRing B] [CommRing K] {n : Type} [Fintype n] [DecidableEq n]

theorem levelvsplit_unitary (τ : B →+* B) (φ : B ≃+* K × K)
    (hτ : ∀ x, φ (τ x) = swapR K (φ x)) (J' : Matrix n n B) (h : GL n B) (hh : h ∈ UJ τ J') :
    ((h : Matrix n n B).map ((RingHom.snd K K).comp φ.toRingHom))ᵀ *
        J'.map ((RingHom.fst K K).comp φ.toRingHom) *
        (h : Matrix n n B).map ((RingHom.fst K K).comp φ.toRingHom) =
      J'.map ((RingHom.fst K K).comp φ.toRingHom) := by
  have hh' : Formalism.UG.cT τ (h : Matrix n n B) * J' * (h : Matrix n n B) = J' := hh
  have key : (Formalism.UG.cT τ (h : Matrix n n B)).map ((RingHom.fst K K).comp φ.toRingHom) =
      ((h : Matrix n n B).map ((RingHom.snd K K).comp φ.toRingHom))ᵀ := by
    ext i j
    simp [Formalism.UG.cT, hτ, Formalism.UG.swapR]
  have h2 := congrArg (fun M : Matrix n n B => M.map ((RingHom.fst K K).comp φ.toRingHom)) hh'
  simp only [Matrix.map_mul] at h2
  rw [key] at h2
  exact h2

theorem levelvsplit_solve (A Ainv P1 P1i P2 : Matrix n n K) (hA : A * Ainv = 1)
    (hP : P1 * P1i = 1) (hrel : P2ᵀ * A * P1 = A) : P2 = (A * P1i * Ainv)ᵀ := by
  have h1 : P2ᵀ * A = A * P1i := by
    calc P2ᵀ * A = P2ᵀ * A * (P1 * P1i) := by rw [hP, Matrix.mul_one]
      _ = P2ᵀ * A * P1 * P1i := by simp only [Matrix.mul_assoc]
      _ = A * P1i := by rw [hrel]
  have h2 : P2ᵀ = A * P1i * Ainv := by
    calc P2ᵀ = P2ᵀ * (A * Ainv) := by rw [hA, Matrix.mul_one]
      _ = P2ᵀ * A * Ainv := by rw [Matrix.mul_assoc]
      _ = A * P1i * Ainv := by rw [h1]
  rw [← h2, Matrix.transpose_transpose]

end Split

end Formalism.UG.P
