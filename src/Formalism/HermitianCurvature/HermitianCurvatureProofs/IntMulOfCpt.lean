module

public import Formalism.HermitianCurvature.StatementNF
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen

@[expose] public section

open MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

namespace Formalism.FourierDecayAlt.P5.HerB

section Wirt

theorem dZ_eq (f : ℂ → ℂ) (c : ℂ) : NF.dZ f c = (1 / 2 : ℂ) * (fderiv ℝ f c 1 - Complex.I * fderiv ℝ f c Complex.I) := rfl

theorem dZ_conj {φ : ℂ → ℂ} {c : ℂ} (h : DifferentiableAt ℝ φ c) :
    NF.dZ (fun w => conj (φ w)) c = conj (NF.dZb φ c) := by
  have hd : HasFDerivAt (fun w => conj (φ w)) ((Complex.conjCLE.toContinuousLinearMap).comp (fderiv ℝ φ c)) c :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp c h.hasFDerivAt
  unfold NF.dZ NF.dZb
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul,
    map_add, Complex.conj_I, map_div₀, map_one, map_ofNat]
  ring

end Wirt

end Formalism.FourierDecayAlt.P5.HerB
