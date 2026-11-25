module

public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVOfNotJump
import Mathlib.Algebra.Order.Star.Int
import Formalism.DistinguishedUnitIdeals.ExistsConstOfInvariantMod
import Formalism.DistinguishedUnitIdeals.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.ArcParametersShiftInvariant

@[expose] public section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03 Module

section Period

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem jb_Fil_anti {a b : ℤ} (hab : a ≤ b) : PD.Fil b ≤ PD.Fil a := by
  obtain ⟨k, rfl⟩ := Int.le.dest hab
  clear hab
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show a + ((k + 1 : ℕ) : ℤ) = a + k + 1 by push_cast; ring]
    exact (PD.Fil_anti (a + k)).trans ih

theorem jb_FilV_anti : Antitone (FilV PD (LL := LL) (V := V)) := by
  intro a b hab
  have h : (PD.Fil b).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp := jb_Fil_anti PD hab
  unfold FilV
  rw [← Submodule.subtype_comp_inclusion _ _ h]
  have e : AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      (((PD.Fil a).restrictScalars Qp).subtype ∘ₗ Submodule.inclusion h) =
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil a).restrictScalars Qp).subtype ∘ₗ
        AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion h) := by
    rw [← AlgebraTensorModule.map_comp, LinearMap.id_comp]
  rw [e]
  exact LinearMap.range_comp_le_range _ _

theorem jb_FilV_exh (y : V ⊗[Qp] BdR) : ∃ a, y ∈ FilV PD (LL := LL) (V := V) a :=
  Pv.LocalLengthBound.rk_filV_exh PD y

theorem jb_FilV_sep (y : V ⊗[Qp] BdR) (hy : ∀ a, y ∈ FilV PD (LL := LL) (V := V) a) : y = 0 :=
  Pv.LocalLengthBound.rk_filV_sep PD y hy

theorem jb_FildR_anti (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) : Antitone (FildR PD ρ τ) :=
  fun _ _ hab => inf_le_inf_left _ (jb_FilV_anti PD hab)

open Formalism.MainNotions.N.Pv.LocalLengthBound in
theorem jb_bound (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (hfin : FiniteDimensional LL ↥(DdRE PD ρ τ)) :
    ∃ a₀ a₁ : ℤ, ∀ a, IsJumpV PD ρ τ a → a₀ ≤ a ∧ a ≤ a₁ := by
  obtain ⟨lo, hlo⟩ := rk_fildR_lo PD ρ τ
  obtain ⟨hi, hhi⟩ := rk_fildR_hi PD ρ τ
  refine ⟨lo, hi - 1, fun a ha => ⟨?_, ?_⟩⟩
  · by_contra! h
    exact ha ((hlo _ (by lia)).trans (hlo _ h.le).symm)
  · by_contra! h
    exact ha ((hhi _ (by lia)).trans (hhi _ (by lia)).symm)

end Period

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    [Fintype (K →ₐ[Qp] LL)]

theorem jumpsBdd_holds (hDR : Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris PD LL) (hK : Function.Bijective (algebraMap K₀ K)) :
    ∀ T : LocLat G Qp LL O, CrysLat PD T → ∃ M h : ZMod n → ℕ, Formalism.MainNotions.LiftingTheory.JumpsLet W T M h := by
  intro T hT
  have hfin : ∀ τ : K →ₐ[Qp] LL, FiniteDimensional LL ↥(DdRE PD T.ρ τ) :=
    fun τ => ((hDR hK T.V T.ρ T.cont hT.2.2.2).2 τ).1
  choose a₀ a₁ hab using fun τ => jb_bound PD T.ρ τ (hfin τ)
  refine ⟨fun _ => Finset.univ.sup (fun τ => (-a₀ τ).toNat),
    fun _ => Finset.univ.sup (fun τ => (a₁ τ).toNat), ?_⟩
  intro i τ _ a ha
  obtain ⟨h0, h1⟩ := hab τ a ha
  have e0 : (-a₀ τ).toNat ≤ Finset.univ.sup (fun τ => (-a₀ τ).toNat) :=
    Finset.le_sup (f := fun τ => (-a₀ τ).toNat) (Finset.mem_univ τ)
  have e1 : (a₁ τ).toNat ≤ Finset.univ.sup (fun τ => (a₁ τ).toNat) :=
    Finset.le_sup (f := fun τ => (a₁ τ).toNat) (Finset.mem_univ τ)
  have f0 := Int.self_le_toNat (-a₀ τ)
  have f1 := Int.self_le_toNat (a₁ τ)
  have g0 : (((-a₀ τ).toNat : ℕ) : ℤ) ≤ ((Finset.univ.sup (fun τ => (-a₀ τ).toNat) : ℕ) : ℤ) := by exact_mod_cast e0
  have g1 : (((a₁ τ).toNat : ℕ) : ℤ) ≤ ((Finset.univ.sup (fun τ => (a₁ τ).toNat) : ℕ) : ℤ) := by exact_mod_cast e1
  simp only [Set.mem_Icc]
  constructor <;> omega

end Formalism.MainNotions.N.Ln03.Pf
