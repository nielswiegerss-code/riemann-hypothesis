module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.ActUDiagMonomial
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.RDIota
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Unimod
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DZTranspose
public import Development.WeilBound.ThetaLifts.TowerModels.PlaneReal

@[expose] public section

open scoped TensorProduct NNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.KSplit

namespace PositivityTheory.SiegelWeilFormula.KSplitA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem det_ne_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  first
  | exact _root_.PositivityTheory.ThKG.Tow.Pln.det_ne_zero_of_hasSig
  | (apply _root_.PositivityTheory.ThKG.Tow.Pln.det_ne_zero_of_hasSig <;> assumption)

theorem fP_unitary {m n : ℕ} (u : Matrix (Fin m) (Fin m) ℂ) (hu : u ∈ Matrix.unitaryGroup (Fin m) ℂ) (P : PX m n)
    (v : Matrix (Fin m) (Fin n) ℂ) : fP P (u * v) = fP (actU u P) v := by
  have key : ∀ i, (∑ a, ‖(u * v) a i‖ ^ 2 : ℝ) = ∑ a, ‖v a i‖ ^ 2 := by
    intro i
    have h1 : ∀ M : Matrix (Fin m) (Fin n) ℂ, ((∑ a, ‖M a i‖ ^ 2 : ℝ) : ℂ) = (Mᴴ * M) i i := by
      intro M
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.ofReal_sum, Complex.ofReal_pow]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Complex.conj_mul']
      rfl
    have h2 : (u * v)ᴴ * (u * v) = vᴴ * v := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ,
        ← Matrix.star_eq_conjTranspose, (Matrix.mem_unitaryGroup_iff').1 hu, Matrix.one_mul]
    exact_mod_cast (h1 (u * v)).trans ((congrArg (fun M => M i i) h2).trans (h1 v).symm)
  have hs : (∑ a, ∑ i, ‖(u * v) a i‖ ^ 2 : ℝ) = ∑ a, ∑ i, ‖v a i‖ ^ 2 := by
    rw [Finset.sum_comm, Finset.sum_comm (f := fun a i => ‖v a i‖ ^ 2)]
    exact Finset.sum_congr rfl fun i _ => key i
  unfold fP
  rw [evX_actU]
  congr 1
  unfold gs
  rw [hs]

theorem mapStar_mul' {p q r : Type} [Fintype q] (A : Matrix p q ℂ) (B : Matrix q r ℂ) :
    (A * B).map star = A.map star * B.map star := by
  ext i j
  simp [Matrix.mul_apply]

end PositivityTheory.SiegelWeilFormula.KSplitA
