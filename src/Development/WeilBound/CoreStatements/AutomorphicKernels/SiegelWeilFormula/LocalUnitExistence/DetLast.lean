module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.InclusionFromRowsIdentityZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Em0Injective
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Ldexb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem det_last {R : Type} [CommRing R] {N n : ℕ} (h : n + 1 = N) (M : Matrix (Fin N) (Fin N) R)
    (hr : ∀ c, M (Ald.i0 h) c = if c = Ald.i0 h then 1 else 0) :
    M.det = (M.submatrix (Ald.em0 h) (Ald.em0 h)).det := by
  subst h
  have e1 : Ald.i0 (rfl : n + 1 = n + 1) = Fin.last n := rfl
  have e2 : Ald.em0 (rfl : n + 1 = n + 1) = Fin.castSucc := by funext i; rfl
  rw [e1] at hr
  rw [e2, Matrix.det_succ_row M (Fin.last n), Finset.sum_eq_single (Fin.last n)]
  · rw [hr, ite_eq_left rfl, Fin.succAbove_last, mul_one]
    have : ((-1 : R) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ))) = 1 := by
      rw [← two_mul, pow_mul]; simp
    rw [this, one_mul]
  · intro c _ hc
    rw [hr c, ite_eq_right hc]; simp
  · simp

end PositivityTheory.SiegelWeilFormula.Ldexb
