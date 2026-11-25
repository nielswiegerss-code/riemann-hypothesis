module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBlochKatoConditionOfWachModules
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Mathlib.Tactic.Linter.Style

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace UpperTheory.N.TBLoc

section Len
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem bd_le_hf (L : Lattice (O := O) ρ) : BD L ≤ HfD PD L := le_sup_right

end Len

end UpperTheory.N.TBLoc

namespace UpperTheory.N.TBLoc
section Clauses
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem tbe_clauses (L : Lattice (O := O) ρ) (I J : Subgroup G) (hIJ : I = J) (e cB : ℕ)
    (h2 : 0 < e → HfD PD L = BD L)
    (h3 : e = 0 → ∀ c : G → V ⧸ L.T, c ∈ HfD PD L ↔ (c ∈ divisibleCocycles L ∧ ∃ x, ∀ g ∈ J, c g = actD L g x - x))
    (hlen : Module.length O ↥(Submodule.torsionBy O (DivisibleCohomology L ⧸ divisibleFiniteCohomology PD L) (((PD.p : ℕ) : O) ^ cB)) ≤
      (((Module.finrank Qp K + 1) * cB : ℕ) : ℕ∞) * lenOl PD (O := O)) :
    (0 < e → divisibleCocycles L ⊓ HfD PD L ≤ BD L) ∧
    (e = 0 → divisibleCocycles L ⊓ HfD PD L = divisibleCocycles L ⊓ (Z1urD L I ⊔ BD L)) ∧
    Module.length O (↥(divisibleCocycles L ⊓ (HfD PD L).comap ((((PD.p : ℕ) : O) ^ cB) • LinearMap.id)) ⧸
        (divisibleCocycles L ⊓ HfD PD L).comap (divisibleCocycles L ⊓ (HfD PD L).comap ((((PD.p : ℕ) : O) ^ cB) • LinearMap.id)).subtype) ≤
      ((Module.finrank Qp K : ℕ∞) + 1) * (cB : ℕ∞) * lenOl PD (O := O) := by
  subst hIJ
  refine ⟨fun he => inf_le_right.trans (h2 he).le, fun he => ?_, ?_⟩
  · apply le_antisymm
    · intro c hc
      rw [Submodule.mem_inf] at hc ⊢
      refine ⟨hc.1, Submodule.mem_sup_left ?_⟩
      exact ((h3 he c).mp hc.2).2
    · intro c hc
      rw [Submodule.mem_inf] at hc ⊢
      obtain ⟨hcZ, hc⟩ := hc
      refine ⟨hcZ, (h3 he c).mpr ⟨hcZ, ?_⟩⟩
      obtain ⟨u, hu, b, hb, rfl⟩ := Submodule.mem_sup.mp hc
      obtain ⟨x, hx⟩ := hu
      obtain ⟨y, rfl⟩ := hb
      refine ⟨x + y, fun g hg => ?_⟩
      simp only [Pi.add_apply, hx g hg, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, map_add (f := _)]
      abel
  · calc _ ≤ _ := GlobalTheory.TBLocal.len_le_torsion PD L _
      _ ≤ _ := hlen
      _ = _ := by push_cast; ring
end Clauses
end UpperTheory.N.TBLoc

namespace UpperTheory.N.TBLoc
section Part1
open Formalism.MainNotions.LocalSituation

variable (S : Sit) [IsTopologicalRing S.LL] [IsDomain S.O] [IsPrincipalIdealRing S.O]
  (Yt : LocLat S.G S.Qp S.LL S.O) (p : Yt.V →ₗ[S.LL] S.LL) (e₀ : Yt.V) (hpe : p e₀ = 1)
  (hp : ∀ g v, p (Yt.ρ g v) = p v) (hint : ∀ v ∈ Yt.L.T, p v ∈ Set.range (algebraMap S.O S.LL))
  (he₀ : e₀ ∈ Yt.L.T) (hinj : Function.Injective (algebraMap S.O S.LL))

include hinj in
theorem tb_part1 (E : S.Comparison₂) (hTB : TBat S E) (e M0 h0 cB : ℕ) (Ve : LocLat S.G S.Qp S.LL S.O)
    (h1 : Module.finrank S.LL Ve.V = 1)
    (hχ : ∀ g x, Ve.ρ g x = ((algebraMap S.Qp S.LL (S.PD.χ g : S.Qp))⁻¹) ^ e • x)
    (hCt : IsCrysOn S S.W.GKs Yt) (hWY : HypW S E (kerY Yt p e₀ hpe hp hint he₀) M0 h0)
    (hc : cTBY S (kerY Yt p e₀ hpe hp hint he₀) M0 h0 e ≤ cB)
    (φ : Yt.V →ₗ[S.O] (Ve.V ⧸ Ve.L.T))
    (hφ : ∀ g, ∀ y ∈ Yt.L.T, p y = 0 → φ (Yt.ρ g y) = actD Ve.L g (φ y)) :
    ((S.PD.p : S.O) ^ cB) • (fun g => φ (Yt.ρ g e₀ - e₀)) ∈ HfD S.PD Ve.L := by
  apply GlobalTheory.TBLocal.tb_part1 <;> assumption

end Part1
end UpperTheory.N.TBLoc

namespace UpperTheory.N.TBLoc
section Eps
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]

theorem eps_lat {V : Type} [AddCommGroup V] [Module LL V] [Module O V] {ρ : Representation LL G V}
    (T : Submodule O V) (e : ℕ) (h : IsMatLat (O := O) (ρ := ρ) T (epsTw PD e)) :
    Module.finrank LL V = 1 ∧ ∀ g x, ρ g x = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e • x := by
  obtain ⟨f, hf, -⟩ := h
  refine ⟨?_, ?_⟩
  · rw [f.finrank_eq, Module.finrank_fin_fun]
  · intro g x
    apply f.injective
    rw [hf, map_smul]
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp [Matrix.mulVec, dotProduct, epsTw, map_inv₀, Units.val_inv_eq_inv_val]
end Eps

end UpperTheory.N.TBLoc
