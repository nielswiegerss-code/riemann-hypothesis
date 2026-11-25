module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DZTranspose
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.BlockTriangularFrames.SiegelParabolicEqStabiliserCols
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.RDIota
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.UnitaryGroupInverseFormula
import Mathlib.Tactic.Linter.Style

@[expose] public section

open scoped TensorProduct NNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.KSplitW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem zeta_inv {ε : ℤˣ} {ζ : ℂ} (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) : ζ⁻¹ = star ζ := by
  rcases hζ with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · simp
  · simp [Complex.inv_I]

theorem dZ_ct {n : ℕ} (a : ℂ) : (dZ n a)ᴴ = dZ n (star a) := by
  rw [Matrix.conjTranspose, Krd.dZ_transpose, Krd.dZ_map_star]

theorem dZ_inv_ct {n : ℕ} {ε : ℤˣ} {ζ : ℂ} (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) :
    dZ n ζ⁻¹ = (dZ n ζ)ᴴ := by
  rw [dZ_ct, zeta_inv hζ]

theorem finOne_mem : finOne F • (1 : AE F E) ∈ intHat F E := by
  refine AddSubgroup.subset_closure ⟨finOne F, ?_, fun v => ?_, 1, ?_⟩
  · show InfiniteAdeleRing.ringEquiv_mixedSpace F (finOne F).1 = 0
    exact map_zero _
  · have e : sndA F (finOne F) = 1 := rfl
    show evalV F v (sndA F (finOne F)) ∈ _
    rw [e, map_one]
    exact one_mem _
  · simp

end PositivityTheory.SiegelWeilFormula.KSplitW
