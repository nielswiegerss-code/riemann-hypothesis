module

public import GroundTheory.ProfiniteCohomology.PoitouTate.PtCompactDualMapEqZeroOfPtCompactToGlobalEqZero
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohCmp
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.ResH1BijectiveOfInverse
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.ResH2BijectiveOfInverse
import GroundTheory.ProfiniteCohomology.CupProducts.Cocycles
import Mathlib.Tactic.Linter.Style

@[expose] public section

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

theorem resCmpChar0' {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (θ : G ≃ₜ* H) {ι : Type} {Lv Hv : ι → Type}
    [∀ v, Group (Lv v)] [∀ v, TopologicalSpace (Lv v)] [∀ v, IsTopologicalGroup (Lv v)]
    [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)] [∀ v, IsTopologicalGroup (Hv v)]
    (lam : ∀ v, Lv v →* G) (hlam : ∀ v, Continuous (lam v)) (φ : ∀ v, Hv v →ₜ* H)
    (ev : ∀ v, Hv v ≃* Lv v) (hev1 : ∀ v, Continuous (ev v)) (hev2 : ∀ v, Continuous (ev v).symm)
    (hev : ∀ v σ, θ (lam v (ev v σ)) = φ v σ) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M) (hc : ContAction rho)
    (A : Rep.{0} (ULift.{0} ℤ) H) [IsDiscreteRep A] (eM : M ≃+ A.V)
    (hM : ∀ g m, eM (rho g m) = A.ρ (θ g) (eM m)) :
    ∃ (E : ↥(H0 rho) ≃+ cohomology A 0)
      (Ev : ∀ v, ↥(H0 (rho.comp (lam v))) ≃+ cohomology (Rep.res (φ v).toMonoidHom A) 0),
      (∀ v x, Ev v (resH0 rho (lam v)  x) = ptRes φ A v 0 (E x)) ∧
      (∀ (z : ↥(H0 rho)) (x : cocycles A 0),
        (∀ s : Fin 0 → H, cochainOf A (cocycleι A 0 x) s = eM z.1) →
        E z = cohomologyπ A 0 x) ∧
      (∀ v (z : ↥(H0 (rho.comp (lam v)))) (x : cocycles (Rep.res (φ v).toMonoidHom A) 0),
        (∀ s : Fin 0 → Hv v, cochainOf _ (cocycleι _ 0 x) s = eM z.1) →
        Ev v z = cohomologyπ _ 0 x) := by
  have hθs : Continuous (θ.symm : H ≃* G).toMonoidHom := θ.symm.continuous
  let rho' : Representation R H M := rho.comp (θ.symm : H ≃* G).toMonoidHom
  have hM' : ∀ h m, eM (rho' h m) = A.ρ h (eM m) := fun h m => by
    show eM (rho (θ.symm h) m) = _
    rw [hM]
    exact congrArg (fun t => A.ρ t (eM m)) (θ.apply_symm_apply h)
  obtain ⟨e0, he0⟩ := CompanionTheory.LocalTateOrthogonality.Gcoh.gc0 H R M rho' A eM hM'
  have hEq : H0 rho = H0 rho' := by
    ext m
    constructor
    · intro hm h
      exact hm _
    · intro hm g
      have := hm (θ g)
      change rho (θ.symm (θ g)) m = m at this
      rwa [θ.symm_apply_apply] at this
  let r0 : ↥(H0 rho) ≃ₗ[R] ↥(H0 rho') := LinearEquiv.ofEq _ _ hEq
  have hloc : ∀ v, ∀ σ m, eM (((rho.comp (lam v)).comp (ev v).toMonoidHom) σ m) =
      (Rep.res (φ v).toMonoidHom A).ρ σ (eM m) := fun v σ m => by
    show eM (rho (lam v (ev v σ)) m) = A.ρ (φ v σ) (eM m)
    rw [hM, hev]
  choose ev0 hev0 using fun v => CompanionTheory.LocalTateOrthogonality.Gcoh.gc0 (Hv v) R M
    ((rho.comp (lam v)).comp (ev v).toMonoidHom) (Rep.res (φ v).toMonoidHom A) eM (hloc v)
  have hEqv : ∀ v, H0 (rho.comp (lam v)) = H0 ((rho.comp (lam v)).comp (ev v).toMonoidHom) := by
    intro v
    ext m
    constructor
    · intro hm h
      exact hm _
    · intro hm g
      have := hm ((ev v).symm g)
      change rho (lam v (ev v ((ev v).symm g))) m = m at this
      rwa [MulEquiv.apply_symm_apply] at this
  let rv : ∀ v, ↥(H0 (rho.comp (lam v))) ≃ₗ[R] ↥(H0 ((rho.comp (lam v)).comp (ev v).toMonoidHom)) :=
    fun v => LinearEquiv.ofEq _ _ (hEqv v)
  refine ⟨r0.toAddEquiv.trans e0, fun v => (rv v).toAddEquiv.trans (ev0 v), fun v z => ?_, fun z x hx => ?_, fun v z x hx => ?_⟩
  have hz' : (z : M) ∈ H0 rho' := hEq ▸ z.2
  obtain ⟨x, hx⟩ := CompanionTheory.LocalTateOrthogonality.Gcoh.exists_coc A 0 (fun _ => eM z.1) (IsLocallyConstant.const _) (by
      refine (CompanionTheory.LocalTateOrthogonality.Gcoh.d_comp rho' A eM hM' 0 fun _ => z.1).trans ?_
      funext s
      rw [CompanionTheory.LocalTateOrthogonality.Gcoh.dn_zero, hz' (s 0), sub_self]
      exact map_zero eM)
  have hE : e0 (r0 z) = cohomologyπ A 0 x := he0 _ x (fun s => congrFun hx s)
  show ev0 v (rv v (resH0 rho (lam v) z)) = ptRes φ A v 0 (e0 (r0 z))
  rw [hE]
  have hP : ptRes φ A v 0 (cohomologyπ A 0 x) =
      cohomologyπ _ 0 (cocyclesMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) 0 x) := by
    unfold ptRes
    exact congrArg (fun f => f.hom x) (cohomologyπ_cohomologyMapAlong (φ v).toMonoidHom
      (continuous_toMonoidHom (φ v)) (𝟙 _) 0)
  rw [hP]
  apply hev0 v
  intro s
  rw [cochainOf_cocycleι_cocyclesMapAlong]
  dsimp only
  rw [hx]
  rfl
  · show e0 (r0 z) = _
    exact he0 _ x (fun s => hx s)
  · show ev0 v (rv v z) = _
    exact hev0 v _ x (fun s => hx s)

end PositivityTheory.Lit1.PTN
