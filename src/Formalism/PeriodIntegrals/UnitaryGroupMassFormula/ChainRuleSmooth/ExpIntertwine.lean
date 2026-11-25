module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightDerivativeSmoothOnIndefiniteUnitaryGroup
public import Formalism.FormalDegreeBessel.StatementG
import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Topology.UniformSpace.Matrix
import Formalism.HermitianCurvature.StatementB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock

@[expose] public section

open Matrix
open scoped ComplexConjugate Nat

namespace CCRuleCW

open Formalism.FourierDecayAlt

section expo

variable {n : ℕ}

theorem exp_intertwine (Y Z H : Matrix (Fin n) (Fin n) ℂ) (h : Y * H = H * Z) :
    NormedSpace.exp Y * H = H * NormedSpace.exp Z := by
  apply GlobalTheory.RightDerivSmooth.exp_intertwine <;> assumption

theorem exp_mem_UH (H Y : Matrix (Fin n) (Fin n) ℂ) (hY : Yᴴ * H + H * Y = 0) :
    NormedSpace.exp Y ∈ Formalism.QuantumDeterminants.UH H := by
  show (NormedSpace.exp Y)ᴴ * H * NormedSpace.exp Y = H
  have h1 : Yᴴ * H = H * (-Y) := by
    rw [Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left hY
  rw [← Matrix.exp_conjTranspose, exp_intertwine _ _ _ h1, Matrix.mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
    NormedSpace.exp_zero, Matrix.mul_one]

theorem UH_mul (H a b : Matrix (Fin n) (Fin n) ℂ) (ha : a ∈ Formalism.QuantumDeterminants.UH H) (hb : b ∈ Formalism.QuantumDeterminants.UH H) :
    a * b ∈ Formalism.QuantumDeterminants.UH H := by
  apply _root_.Formalism.FourierDecayAlt.P.TwoByOneBlock.UH_mul <;> assumption

theorem lie_smul (H X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ * H + H * X = 0) (c : ℝ) :
    ((c : ℂ) • X)ᴴ * H + H * ((c : ℂ) • X) = 0 := by
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
    Matrix.mul_smul, ← smul_add, hX, smul_zero]

end expo


end CCRuleCW
