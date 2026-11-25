module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionLiftPairStepVectorInvLevelCharStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift.LevelFix

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem realDatum_identity_lifts_identity (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) :
    IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) 1 1 :=
  ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact rTup_one⟩

theorem levChi_flag_one (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) :
    levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) 1 = 1 := by
  have := (levChar D.sp.cm (Vc D i).gram (R.βV i) (flagL (R.datVt i t))).map_one
  unfold levChi
  rw [map_one]
  exact congrArg Units.val this

end GlobalTheory.RawLift.LevelFix
