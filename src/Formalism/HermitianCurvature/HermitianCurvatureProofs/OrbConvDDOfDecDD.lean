module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaContOn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CkOnZeroOfContOn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace Formalism.FourierDecayAlt.P.S3dx4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem ag_nonneg (k r : ℕ) : 0 ≤ AG k r := by unfold AG; positivity

theorem gap4 {k r : ℕ} {h : ℝ} (hG : GapOK k r h) :
    9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 3 * AG k r + 3 ≤ aOf r h := hG.2.2.2

theorem rho_triv {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (p : B.SS k r)
    (F : B.Mat k r → (ℂ →L[ℂ] ℂ)) (g : B.Mat k r) : B.rho (triv D) p F g = F (B.sgs p g) := by
  ext
  simp [B.rho, triv]

theorem rpow_bound (t C a : ℝ) (ht : 0 ≤ t) (ha : a ≠ 0) : t ^ a * (C * t ^ (-a)) ≤ |C| := by
  rcases ht.lt_or_eq with h | h
  · rw [mul_left_comm, ← Real.rpow_add h, add_neg_cancel, Real.rpow_zero, mul_one]
    exact le_abs_self C
  · subst h
    rw [Real.zero_rpow ha, zero_mul]
    exact abs_nonneg C

end Formalism.FourierDecayAlt.P.S3dx4
