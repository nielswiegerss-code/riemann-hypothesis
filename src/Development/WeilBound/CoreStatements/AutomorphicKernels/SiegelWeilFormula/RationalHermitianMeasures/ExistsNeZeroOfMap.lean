module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps

@[expose] public section

set_option linter.unusedSectionVars false

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp

namespace PositivityTheory.SiegelWeilFormula.MeasD

open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.kfour

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem conj_sym {ι κ : Type} [Fintype ι] (hσ : ∀ a, σ (σ a) = a) (P : Matrix ι κ E) (M : Matrix ι ι E) (s : E)
    (hM : ∀ i j, σ (M j i) = s * M i j) (i j : κ) :
    σ ((Pᵀ * M * P.map σ) j i) = s * (Pᵀ * M * P.map σ) i j := by

  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσ, hM, Finset.mul_sum,
  Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem frame_sign (hσ : ∀ a, σ (σ a) = a) {n : ℕ} (hn : 1 ≤ n) (J : Matrix (Fin n) (Fin n) E) (s : E)
    (hJ : ∀ i j, σ (J j i) = s * J i j) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ)
    (hb : b.1ᵀ * dbl J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) : (((ε : ℤ) : E)) = s := by
  have hD : ∀ i j, σ (dbl J j i) = s * dbl J i j := by
    rintro (i | i) (j | j) <;> simp [dbl, hJ]
  have h := conj_sym hσ b.1 (dbl J) s hD (Sum.inl ⟨0, hn⟩) (Sum.inr ⟨0, hn⟩)
  rw [hb] at h
  simpa using h

theorem ne_zero_of_sig {m r s : ℕ} (hm : 1 ≤ m) (M : Matrix (Fin m) (Fin m) ℂ) (h : HasSig M r s) : M ≠ 0 := by
  rintro rfl
  obtain ⟨hrs, A, hA⟩ := h
  simp only [Matrix.mul_zero, Matrix.zero_mul] at hA
  rcases Nat.eq_zero_or_pos r with hr | hr
  · have hs : 0 < s := by omega
    have := congrFun (congrFun hA (Sum.inr ⟨0, hs⟩)) (Sum.inr ⟨0, hs⟩)
    simp at this
  · have := congrFun (congrFun hA (Sum.inl ⟨0, hr⟩)) (Sum.inl ⟨0, hr⟩)
    simp at this

theorem exists_ne_zero_of_map {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (f : E →+* ℂ) (c : ℂ) (h : c • J.map f ≠ 0) :
    ∃ i j, J i j ≠ 0 := by
  by_contra! hc
  apply h
  ext i j
  simp [hc i j]

end PositivityTheory.SiegelWeilFormula.MeasD
