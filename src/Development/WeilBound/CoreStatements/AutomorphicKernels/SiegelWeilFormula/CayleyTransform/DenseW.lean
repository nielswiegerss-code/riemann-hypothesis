module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.OrthogonalFormMulTranspose
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.RDIota
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.UnitaryGroupInverseFormula
import Mathlib.Tactic.Linter.Style

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Krd.DM

open PositivityTheory.SiegelWeilFormula.Krd.DC

theorem conj_unitE {K ι : Type} [CommRing K] [Fintype ι] [DecidableEq ι] (f : K →+* K) (b bi Z D Q : Matrix ι ι K)
    (hb : b * bi = 1) (hQ : bᵀ * D * b.map f = Q) (hZ : Zᵀ * Q * Z.map f = Q) :
    (b * Z * bi)ᵀ * D * (b * Z * bi).map f = D := by
  have h1 : (1 : Matrix ι ι K).map f = 1 := Matrix.map_one _ (map_zero f) (map_one f)
  have hD : D = biᵀ * Q * bi.map f := by
    calc D = (b * bi)ᵀ * D * (b * bi).map f := by
          rw [hb, Matrix.transpose_one, h1, Matrix.one_mul, Matrix.mul_one]
      _ = biᵀ * (bᵀ * D * b.map f) * bi.map f := by
          rw [Matrix.transpose_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
      _ = biᵀ * Q * bi.map f := by rw [hQ]
  calc (b * Z * bi)ᵀ * D * (b * Z * bi).map f = biᵀ * (Zᵀ * (bᵀ * D * b.map f) * Z.map f) * bi.map f := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.map_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
    _ = D := by rw [hQ, hZ, ← hD]

theorem det_ne_of {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] (f : K →+* K) {A D : Matrix ι ι K}
    (h : Aᵀ * D * A.map f = D) (hD : D.det ≠ 0) : A.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul] at this
  exact hD this.symm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem incM_cA {p q : Type} (M : Matrix p q E) : (incM F M).map (cA σ) = incM F (M.map σ) := by
  ext i j
  rfl

theorem incM_alt_bis {p q : Type} (M : Matrix p q E) : (incM F M)ᵀ = incM F Mᵀ :=
  Matrix.transpose_map.symm

variable (d : SD σ)

theorem J_unit (ε : ℤˣ) {n : ℕ} : IsUnit (Qc n ε)ᵀ.det := by
  refine Matrix.isUnit_det_of_right_inverse (B := ((ε : ℤ) : ℂ)⁻¹ • (Qc n ε)ᵀ) ?_
  rw [Matrix.mul_smul, J_sq, smul_smul, inv_mul_cancel₀ (eps_ne ε), one_smul]

theorem det_of_inU {ε : ℤˣ} {n : ℕ} {h : M2 n} (hh : InU (Qc n ε)ᵀ h) : IsUnit h.det := by
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  have := congrArg Matrix.det hh
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
  exact (J_unit ε).ne_zero this.symm

end PositivityTheory.SiegelWeilFormula.Krd.DM
