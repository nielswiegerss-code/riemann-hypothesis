module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PostOnGaLMemGoodPart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionEqZeroOfNoLift

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR
  Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.KeepLevel

open GlobalTheory.Mem GlobalTheory.Mem.Th GlobalTheory.ChainEquiv

section General

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)}
  {L : LevDat D.host.E ℂ V.rank}

theorem levChi_withP (P : LevelP L.Pg L.r ℂ) (p : P.H) {κ : GA D V} (hκ : IsLevelLift V β L p κ) :
    levChi V β (withP L P) κ = ((P.chi p : ℂˣ) : ℂ) * levChi V β (flagL L) κ := by
  unfold levChi
  rw [levFn_withP, hκ.2.2, extendOne_of_mem _ p.2, Units.val_mul]

theorem eigen_of_hasType {P : LevelP L.Pg L.r ℂ} {f : GA D V → ℂ} (hf : HasType V β (withP L P) f) (p : P.H) {κ : GA D V}
    (hκ : IsLevelLift V β L p κ) (h : GA D V) : ((P.chi p : ℂˣ) : ℂ) * f h = (levChi V β (flagL L) κ)⁻¹ * f (h * κ) := by
  have hp : rTup β L (finE V κ) ∈ P.H := hκ.2.2.symm ▸ p.2
  have ha := levChi_ne_zero (β := β) (flagL L) κ
  rw [hf κ ⟨hκ.1, hκ.2.1, hp⟩ h, levChi_withP P p hκ]
  field_simp

theorem hasType_of_eigen {P : LevelP L.Pg L.r ℂ} {f : GA D V → ℂ}
    (hf : ∀ (p : P.H) κ, IsLevelLift V β L p κ → ∀ h, ((P.chi p : ℂˣ) : ℂ) * f h = (levChi V β (flagL L) κ)⁻¹ * f (h * κ)) :
    HasType V β (withP L P) f := by
  intro κ hκ h
  have hp : rTup β L (finE V κ) ∈ P.H := hκ.2.2
  have hl : IsLevelLift V β L (⟨_, hp⟩ : P.H) κ := ⟨hκ.1, hκ.2.1, rfl⟩
  have ha := levChi_ne_zero (β := β) (flagL L) κ
  rw [levChi_withP P _ hl, mul_right_comm, hf _ κ hl h]
  field_simp

theorem mem_mult_of_level {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} {X : MMap M} (hX : X ∈ Mult θ M J χ)
    (h : ∀ v, ∀ k ∈ J', ∀ g, X v (g * k) = χ' k * X v g) : X ∈ Mult θ M J' χ' :=
  have a := (GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ X).1 hX
  Submodule.subset_span ⟨a.aut, a.cusp, h, a.equiv, a.cont⟩

theorem hasType_of_comm (hL : LiftsExist V β L) {P : LevelP L.Pg L.r ℂ} (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) {f : GA D V → ℂ}
    (h1 : HasType V β (flag1L L) f) (h2 : HasType V β (flag1L L) (e f)) (hf : HasType V β (withP L P) f)
    (hc : ∀ g, e (actL V β L g f) = actL V β L g (e f)) : HasType V β (withP L P) (e f) := by
  refine IsPLevel.hasType ⟨h2, fun p => ?_⟩
  obtain ⟨κ, hκ⟩ := hL p
  have a : actL V β L p f = ((P.chi p : ℂˣ) : ℂ) • f := funext fun h =>
    (level_action_spec h1 ⟨κ, hκ⟩ κ hκ h).trans (eigen_of_hasType hf p hκ h).symm
  exact (hc p).symm.trans ((congrArg e a).trans (e.map_smul _ f))

end General

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem mem_lvlPart_iff (P : LevelP R.Pg D.R.r ℂ) (t : T) (j : ℕ) (U : R.CC t j) :
    U ∈ lvlPart R P t j ↔ ∀ p : P.H, Rel R t p j U (((P.chi p : ℂˣ) : ℂ) • U) := by
  constructor
  · intro hU p κ hκ v h
    have a : (U : SmT (R.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) ∈ MultT R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j P))
      (levChi _ (R.βY j) (R.datYt t j P)) := (mem_multT R.θ (R.MY j) _ _ _).2 hU
    exact eigen_of_hasType (L := R.datYt t j R.triv) (P := P) (multT_value _ _ _ _ _ a v).2 p hκ h
  · intro hU
    refine mem_mult_of_level ((mem_multT R.θ (R.MY j) _ _ _).1 U.2) fun v => ?_
    exact hasType_of_eigen (L := R.datYt t j R.triv) (P := P) fun p κ hκ h => hU p κ hκ (PiTensorProduct.tprod ℂ v) h

theorem goodProjector_levelMultiplicitySpace_mem_goodRows (hl : R.toLevCh.Is A.μ0) (hi : R.models_inf) (hr : R.grp_record) (P : LevelP R.Pg D.R.r ℂ) (t : T)
    {X : MMap (R.MY 0)} (hX : X ∈ multAt R P t 0) : postOn (R.MY 0) R.e0 X ∈ R.EEat P := by
  have h0 := multAt_le R P t 0 hX
  rw [multAt_zero] at h0 hX
  have hL := GlobalTheory.ProjectedLift.liftsExist_rows R hl
  have h1 : postOn (R.MY 0) R.e0 X ∈ R.EEat R.triv :=
    GlobalTheory.ProjectedLift.postOn_gaL_mem_goodPart (L := R.dat0 R.triv) hi hL R.eG _ (GlobalTheory.ProjectedLift.eC_conv R hr) h0
  refine ⟨mem_mult_of_level h1.1 fun v => ?_, h1.2⟩
  have a0 : HasType _ (R.βY 0) (R.dat0 R.triv) (X v) := ((GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ X).1 h0).lev v
  refine hasType_of_comm (L := R.dat0 R.triv) (P := P) hL R.e0 a0
    (((GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ _).1 h1.1).lev v) (((GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ X).1 hX).lev v) fun g => ?_
  obtain ⟨g, rfl⟩ := R.eG.surjective g
  exact (GlobalTheory.ProjComm.proj_comm R hl hr).1 g _ a0

end GlobalTheory.KeepLevel
