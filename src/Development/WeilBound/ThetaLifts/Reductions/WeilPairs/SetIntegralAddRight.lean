module

public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SplitPlaceSiegelLawDiagonalLagrangianCharacterIm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrIntRhoInv
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

@[expose] public section

open scoped TensorProduct Matrix Pointwise
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.SplitLagrF

section aux
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hOF_dC (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (a b : WOF F E nS nT) :
    hOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) (dC F E nT * a) (dC F E nT * b) = 0 := by
  have ha : dC F E nT * a = Matrix.of fun i j => a (Sum.elim id id (finSumFinEquiv.symm i)) j :=
    GlobalTheory.LagrThetaInv.dC_mul_eq a
  have hb : dC F E nT * b = Matrix.of fun i j => b (Sum.elim id id (finSumFinEquiv.symm i)) j :=
    GlobalTheory.LagrThetaInv.dC_mul_eq b
  rw [ha, hb]
  unfold hOF
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
  simp only [← finSumFinEquiv.sum_comp, Matrix.of_apply, Equiv.symm_apply_apply, GlobalTheory.LagrThetaInv.dblG_apply]
  simp only [Fintype.sum_sum_type]
  simp [dbl, Finset.sum_neg_distrib]

theorem symplOHF_dC (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (ξ₀ : E) (a b : WOF F E nS nT) :
    symplOHF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ (dC F E nT * a) (dC F E nT * b) = 0 := by
  simp only [symplOHF, symplOF, hOF_dC, mul_zero, map_zero]

theorem dC_mul_ratWF {nS nT : ℕ} (γ : Matrix (Fin nT) (Fin nS) E) :
    (dC F E nT * (ratWF γ : WOF F E nS nT) : WOF F E nS (nT + nT)) = ratWF (GlobalTheory.LagrThetaInv.dC E nT * γ) :=
  GlobalTheory.LagrThetaInv.dC_mul_rat γ

theorem setIntegral_add_right {nS nT : ℕ} (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT))
    [ν.IsAddHaarMeasure] (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) (g : WOF F E nS nT → ℂ)
    (h2 : ∀ (r : ratLF F E nS nT) (v : WOF F E nS nT), g (r +ᵥ v) = g v) (u : WOF F E nS nT) :
    ∫ v in 𝓕, g (v + u) ∂ν = ∫ v in 𝓕, g v ∂ν := by
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : ContinuousAdd (WOF F E nS nT) := inferInstanceAs (ContinuousAdd (Fin nT → Fin nS → AF F ⊗[F] E))
  haveI : MeasurableAdd (WOF F E nS nT) :=
    ⟨fun c => (continuous_const_add c).measurable, fun c => (continuous_add_const c).measurable⟩
  haveI : MeasurableConstVAdd (ratLF F E nS nT) (WOF F E nS nT) :=
    ⟨fun r => (continuous_const_add (r : WOF F E nS nT)).measurable⟩
  haveI : VAddInvariantMeasure (ratLF F E nS nT) (WOF F E nS nT) ν :=
    ⟨fun r s _ => measure_preimage_add ν (r : WOF F E nS nT) s⟩
  haveI : VAddCommClass (WOF F E nS nT) (ratLF F E nS nT) (WOF F E nS nT) :=
    ⟨fun a r x => add_left_comm a (r : WOF F E nS nT) x⟩
  haveI : Countable (ratLF F E nS nT) := by
    haveI : Countable E := by
      haveI : FiniteDimensional ℚ E := inferInstance
      exact ((Module.finBasis ℚ E).equivFun).injective.countable
    have : Countable (Matrix (Fin nT) (Fin nS) E) := inferInstanceAs (Countable (Fin nT → Fin nS → E))
    exact (Set.countable_range ((incAF F E).toAddMonoidHom.mapMatrix (m := Fin nT) (n := Fin nS))).to_subtype
  rw [← (measurePreserving_add_right ν u).setIntegral_image_emb (measurableEmbedding_addRight u) g 𝓕]
  have hF' : IsAddFundamentalDomain (ratLF F E nS nT) ((· + u) '' 𝓕) ν := by
    have hs : (· + u) '' 𝓕 = ((u : WOF F E nS nT) +ᵥ 𝓕 : Set (WOF F E nS nT)) := by
      rw [← Set.image_vadd]
      congr 1
      funext v
      exact add_comm v u
    rw [hs]
    exact h𝓕.vadd_of_comm (G' := WOF F E nS nT) (u : WOF F E nS nT)
  exact hF'.setIntegral_eq h𝓕 h2

end aux

end GlobalTheory.SplitLagrF
