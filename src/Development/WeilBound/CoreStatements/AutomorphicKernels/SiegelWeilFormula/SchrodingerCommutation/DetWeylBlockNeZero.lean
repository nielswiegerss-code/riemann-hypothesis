module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.tweyl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

omit [NumberField F] [NumberField E] in
theorem int_units_sq (ε : ℤˣ) {R : Type} [CommRing R] : ((ε : ℤ) : R) * ((ε : ℤ) : R) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

omit [NumberField F] [NumberField E] in
theorem det_weyl_block_ne_zero {n : ℕ} (ε : ℤˣ) :
    (Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) E) (1 : Matrix (Fin n) (Fin n) E) (((ε : ℤ) : E) • (1 : Matrix (Fin n) (Fin n) E)) (0 : Matrix (Fin n) (Fin n) E)).det ≠ 0 := by
  set M := Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) E) (1 : Matrix (Fin n) (Fin n) E) (((ε : ℤ) : E) • (1 : Matrix (Fin n) (Fin n) E)) (0 : Matrix (Fin n) (Fin n) E)
  have hM : M * (((ε : ℤ) : E) • M) = 1 := by
    simp only [M, Matrix.mul_smul, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero, Matrix.fromBlocks_smul, smul_zero, smul_smul, int_units_sq, one_smul,
      Matrix.fromBlocks_one]
  intro h0
  have := congrArg Matrix.det hM
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

variable (d : SD σ)

omit [NumberField F] [NumberField E] in
theorem siegel_factor_ne {G H : Type} [Group G] [Group H] (χ : G →* Circle) (u : G) (m : H →* ℝ≥0) (v : H) (r : ℝ) :
    (χ u : ℂ) * (((m v : ℝ) ^ r : ℝ) : ℂ) ≠ 0 := by
  have hv : m v ≠ 0 := fun h => by
    have := map_mul m v v⁻¹
    rw [mul_inv_cancel, map_one, h, zero_mul] at this
    exact one_ne_zero this
  refine mul_ne_zero (Circle.coe_ne_zero _) (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos ?_ _).ne')
  exact lt_of_le_of_ne (NNReal.coe_nonneg _) (by exact_mod_cast hv.symm)

end PositivityTheory.SiegelWeilFormula.tweyl
