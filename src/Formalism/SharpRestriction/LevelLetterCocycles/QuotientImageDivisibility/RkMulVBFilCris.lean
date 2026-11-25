module

import Formalism.SharpRestriction.LevelLetterCocycles.JsetEmb
import Formalism.SharpRestriction.LevelLetterCocycles.UniversalGeneralOfRestriction
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains

@[expose] public section

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

section Ops

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem rk_mem_Dcris {x : V ⊗[Qp] B} : x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]

theorem rk_mem_DcrisL (τ : K₀ →ₐ[Qp] LL) {x : V ⊗[Qp] B} :
    x ∈ DcrisL PD ρ τ ↔ x ∈ Dcris PD ρ ∧
      ∀ c, mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x = τ c • x := by
  simp only [DcrisL, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem rk_act_mulVB (g : G) (c : K₀) (x : V ⊗[Qp] B) :
    actVB PD ρ g (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x) =
      mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c (actVB PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul w b => simp [actVB, mulVB, map_mul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem rk_mulVB_Dcris (c : K₀) {x : V ⊗[Qp] B} (hx : x ∈ Dcris PD ρ) :
    mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x ∈ Dcris PD ρ := by
  rw [rk_mem_Dcris] at hx ⊢
  intro g
  rw [rk_act_mulVB, hx g]

theorem rk_ιV_mul (c : K₀) (y : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c y) =
      mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (algebraMap K₀ K c)
        (ιV PD (LL := LL) (V := V) y) := Formalism.MainNotions.UnusedSlot80.UnivC.ιV_mul c y

theorem rk_mulVdR_FilV (c : K) (a : ℤ) {y : V ⊗[Qp] BdR} (hy : y ∈ FilV PD (LL := LL) (V := V) a) :
    mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c y ∈ FilV PD (LL := LL) (V := V) a := by
  intros
  apply _root_.Formalism.MainNotions.N.JsetEmb.de_rham_mul_filtration_stable <;> assumption

theorem rk_mulVB_FilCris (c : K₀) (a : ℤ) {x : V ⊗[Qp] B} (hx : x ∈ FilCris PD ρ a) :
    mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x ∈ FilCris PD ρ a := by
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hx
  refine Submodule.mem_inf.2 ⟨rk_mulVB_Dcris PD ρ c h1, ?_⟩
  rw [Submodule.mem_comap] at h2 ⊢
  rw [rk_ιV_mul]
  exact rk_mulVdR_FilV PD _ a h2

theorem rk_mapVB_mulVB {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (f : V →ₗ[LL] V') (c : K₀) (x : V ⊗[Qp] B) :
    Formalism.MainNotions.RamifiedCoefficientChains.mapVB LL f (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x) =
      mulVB (K₀ := K₀) (B := B) (V := V') (LL := LL) c (Formalism.MainNotions.RamifiedCoefficientChains.mapVB LL f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul w b => simp [Formalism.MainNotions.RamifiedCoefficientChains.mapVB, mulVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem rk_ιV_inj : Function.Injective (ιV PD (LL := LL) (V := V)) := by
  apply _root_.Formalism.MainNotions.UnusedSlot80.UnivF.ιV_inj <;> assumption

end Ops

end Formalism.MainNotions.N.Pv.LocalLengthBound
