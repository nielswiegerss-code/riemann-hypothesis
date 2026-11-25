module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Formalism.UnipotentAdelicQuotients.SWXSDefs

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.ThetaDictR

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sig_invol (hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  rw [hcm.2.2.2, hcm.2.2.2, star_star]


omit [NumberField F] [NumberField E] in
theorem conj_form {ι κ : Type} [Fintype ι] [Fintype κ] (hσ : ∀ x, σ (σ x) = x) (M : Matrix κ κ E) (b : Matrix κ ι E)
    (s : E) (hM : ∀ k l, σ (M l k) = s * M k l) (i j : ι) :
    σ ((bᵀ * M * b.map σ) j i) = s * (bᵀ * M * b.map σ) i j := by

  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσ, hM, Finset.mul_sum,
  Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

omit [NumberField F] [NumberField E] in
theorem dbl_conj {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (s : E) (hJ : ∀ i j, σ (J j i) = s * J i j)
    (k l : Fin n ⊕ Fin n) : σ (GlobalTheory.WeilM.dbl J l k) = s * GlobalTheory.WeilM.dbl J k l := by
  rcases k with k | k <;> rcases l with l | l <;> simp [GlobalTheory.WeilM.dbl, hJ]

end PositivityTheory.SiegelWeilFormula.ThetaDictR
