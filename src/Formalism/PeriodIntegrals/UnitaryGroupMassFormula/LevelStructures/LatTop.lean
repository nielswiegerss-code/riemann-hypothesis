module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVSDBwdHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.IsCompactSpanRange

@[expose] public section

namespace MassDataLevelSSteps.LatTop

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures MeasureTheory NumberField IsDedekindDomain
  Topology PI.AdicCompletionValuation

section Key

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem exists_int_smul_mem (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ N : ℤ, N ≠ 0 ∧ N • x ∈ L := by
  apply Formalism.L2.SG.Pf.NcVal.OmVSt.OmX.exists_int_smul_mem <;> assumption

end Key

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

theorem smul_mem_latLoc (Λ : Set (Fin n → E)) {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F)
    {y : Fin n → Fv F v ⊗[F] E} (hy : y ∈ latLoc (E := E) v Λ) : c • y ∈ latLoc (E := E) v Λ :=
  (latLoc (E := E) v Λ).smul_mem (⟨c, hc⟩ : v.adicCompletionIntegers F) hy

theorem isCompact_latLoc (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) :
    IsCompact (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) :=
  PI.OmLocU.isCompact_latLoc v _ ⟨L, Submodule.IsLattice.of_fg E hfg, rfl⟩

theorem one_tmul_intCast_mul (N : ℤ) (e : E) :
    (1 : Fv F v) ⊗ₜ[F] ((N : E) * e) = (N : Fv F v) ⊗ₜ[F] e := by
  induction N using Int.induction_on with
  | zero => simp
  | succ k ih =>
    push_cast at ih ⊢
    rw [add_mul, one_mul, TensorProduct.tmul_add, ih, TensorProduct.add_tmul]
  | pred k ih =>
    push_cast at ih ⊢
    rw [sub_mul, one_mul, TensorProduct.tmul_sub, ih, TensorProduct.sub_tmul]

theorem ratV_zsmul_single (N : ℤ) (j : Fin n) (e : E) :
    ratV (F := F) (Fv F v) (N • (Pi.single j e : Fin n → E)) =
      (N : Fv F v) • (Pi.single j ((1 : Fv F v) ⊗ₜ[F] e) : Fin n → Fv F v ⊗[F] E) := by
  classical
  funext i
  by_cases h : i = j
  · subst h
    simp [ratV, inclR, TensorProduct.smul_tmul']
    exact one_tmul_intCast_mul v N e
  · simp [ratV, inclR, h]

end Lat

end MassDataLevelSSteps.LatTop
