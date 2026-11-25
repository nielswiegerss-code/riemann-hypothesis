module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RationalPointsAdelicUnitaryEqUnitary

@[expose] public section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section Generic

variable {A : Type} [CommRing A] {n : ℕ}

theorem hform_eq_dot (σ : A →+* A) (M : Matrix (Fin n) (Fin n) A) (x y : Fin n → A) :
    Formalism.UG.hform σ M x y = (fun i => σ (x i)) ⬝ᵥ (M *ᵥ y) := by
  show (∑ i, ∑ j, σ (x i) * M i j * y j) = ∑ i, σ (x i) * ∑ j, M i j * y j
  simp only [Finset.mul_sum, mul_assoc]

theorem hform_mulVec (σ : A →+* A) (J M : Matrix (Fin n) (Fin n) A) (x y : Fin n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ M * J * M) x y := by
  apply _root_.GlobalTheory.Member.RatElt.hform_mulVec <;> assumption

theorem hform_ext (σ : A →+* A) (M₁ M₂ : Matrix (Fin n) (Fin n) A)
    (h : ∀ x y, Formalism.UG.hform σ M₁ x y = Formalism.UG.hform σ M₂ x y) : M₁ = M₂ := by
  ext i j
  have hij := h (Pi.single i 1) (Pi.single j 1)
  first
    | simpa [Formalism.UG.hform, Pi.single_apply, apply_ite σ] using hij

end Generic

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem sc_mul (a b : Fv F v) : sc (E := E) v (a * b) = sc (E := E) v a * sc (E := E) v b := by
  simp only [sc, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem sc_one : sc (E := E) v (1 : Fv F v) = 1 := rfl

theorem split_decomp {e : Fv F v ⊗[F] E} {π₁ π₂ : Fv F v ⊗[F] E →+* Fv F v}
    (h1 : ∀ x, x * e = sc (E := E) v (π₁ x) * e) (h2 : ∀ x, x * (1 - e) = sc (E := E) v (π₂ x) * (1 - e))
    (x : Fv F v ⊗[F] E) : x = sc (E := E) v (π₁ x) * e + sc (E := E) v (π₂ x) * (1 - e) := by
  linear_combination h1 x + h2 x

theorem split_ext {e : Fv F v ⊗[F] E} {π₁ π₂ : Fv F v ⊗[F] E →+* Fv F v}
    (h1 : ∀ x, x * e = sc (E := E) v (π₁ x) * e) (h2 : ∀ x, x * (1 - e) = sc (E := E) v (π₂ x) * (1 - e))
    {x y : Fv F v ⊗[F] E} (hx : π₁ x = π₁ y) (hy : π₂ x = π₂ y) : x = y := by
  rw [split_decomp v h1 h2 x, split_decomp v h1 h2 y, hx, hy]

end Split

end PI.LocMassTypW
