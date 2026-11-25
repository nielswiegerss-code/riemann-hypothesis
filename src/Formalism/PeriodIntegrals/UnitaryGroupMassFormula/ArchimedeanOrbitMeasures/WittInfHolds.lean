module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.HaarUniqInfHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.UnitChoice
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.HformEntry
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.InclRAlgebraMap
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.LocalSum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.StFix
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.StLamOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DetNZHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianDiagonalization.ExistsOrthogonalFamily
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExStabOrb
import Mathlib.Tactic.Linter.Style

@[expose] public section

namespace PI.AprimeInfWitt

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField Matrix Formalism.UG PI.VolStabS.OrbR
open scoped TensorProduct

theorem witt_R {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h2 : Module.finrank F E = 2) (hfix : ∀ a : E, σ a = a ↔ a ∈ (algebraMap F E).range)
    (hinv : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) {a : ℕ}
    (X0 : Fin a → Fin M → E) (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j)
    (hdet : (gramE σ J X0).det ≠ 0) (R : Type) [CommRing R] [Algebra F R]
    (hU : PIW.AdelicOrbitU.UnitChoice R) (y : Fin a → Fin M → R ⊗[F] E)
    (hy : gramR R σ J y = (gramE σ J X0).map (inclR R)) :
    ∃ g : HA R σ J, g • ratTup (F := F) R X0 = y :=
  PI.VolStabS.witt_R σ h2 hfix hinv J hJ X0 hT hdet R hU y hy

end PI.AprimeInfWitt

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem wittInf_holds : WittInf := by
  intro D X u' ψ hT μinf νinf fibInf hP y hy
  have h2 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have hfix : ∀ a : X.B.I.E, X.B.I.cm.sig a = a ↔ a ∈ (algebraMap X.B.I.F X.B.I.E).range :=
    fun a => X.B.I.cm.fixed a
  have hinv : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x := fun x => star_star x
  have hJ : IsHermND X.B.I.cm.sig X.B.I.J := by
    refine ⟨fun i j => ?_, X.B.I.J_det⟩
    have := congrFun (congrFun X.B.I.J_herm i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
    exact this
  have hdet := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  have hU : PIW.AdelicOrbitU.UnitChoice (Ainf X.B.I.F) :=
    PIW.AdelicOrbitU.uc_pi (fun v : NumberField.InfinitePlace X.B.I.F => v.Completion)
  have hyG : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J y =
      (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) :=
    Set.mem_singleton_iff.1 (Set.mem_preimage.1 hy.1)
  obtain ⟨g, hg⟩ := PI.AprimeInfWitt.witt_R X.B.I.cm.sig h2 hfix hinv X.B.I.J hJ (tupH (frameOf X u')) hT hdet
    (Ainf X.B.I.F) hU y hyG
  exact ⟨g, hg⟩

end PI.AprimeInfW
