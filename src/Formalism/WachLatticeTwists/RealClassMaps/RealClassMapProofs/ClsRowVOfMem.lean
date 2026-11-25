module

public import Formalism.WachLatticeTwists.ShapeRowIsomorphisms.StatClause5Row
public import Formalism.WachLatticeTwists.ShapeRowIsomorphisms.Statement

@[expose] public section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsCycOn IsFGTop cupFG toH1Cocycles traceH1 transportCocycles)

namespace Formalism.RepresentationBoundsCohomology.FIN

theorem kRowRange (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    (VT VT' : Type)
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
    (G : Type) [Group G] [TopologicalSpace G] (D : LatData O G VT VT')
    (M : Type) [AddCommGroup M] [Module O M] (ρM : Representation O G M)
    (u : M ≃ₗ[O] (VT ⧸ D.T)) (hu : ∀ g m, u (ρM g m) = D.ρA g (u m))
    (hopen : IsOpen (D.T : Set VT)) : LinearMap.range (kRow D ρM u hu) = lcH1 ρM := by
  have hdisc : DiscreteTopology (VT ⧸ D.T) :=
    QuotientAddGroup.discreteTopology (N := D.T.toAddSubgroup) hopen
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    induction y using Submodule.Quotient.induction_on with
    | _ c =>
      refine ⟨transportCocycles (MulEquiv.refl G) u ρM D.ρA hu ⟨c.1, c.2.2⟩, ?_, rfl⟩
      have h1 : IsLocallyConstant c.1 := (IsLocallyConstant.iff_continuous _).2 c.2.1
      exact h1.comp u.symm
  · rintro _ ⟨c, hc, rfl⟩
    have hc' : IsLocallyConstant (c : G → M) := hc
    have h3 : (fun g : G => u ((c : G → M) g)) ∈ Z1 D.ρA := by
      refine ⟨(hc'.comp u).continuous, fun a b => ?_⟩
      beta_reduce
      rw [c.2, map_add (f := _), hu]
    refine ⟨Submodule.Quotient.mk ⟨_, h3⟩, ?_⟩
    refine congrArg (Submodule.mkQ _) (Subtype.ext (funext fun g => ?_))
    change u.symm (u ((c : G → M) g)) = _
    rw [LinearEquiv.symm_apply_apply]

theorem resLC (O G M : Type) [CommRing O] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module O M]
    (ρ : Representation O G M) (Dw : Subgroup G) :
    lcH1 ρ ≤ (lcH1 (resRep ρ Dw)).comap (resH1 ρ Dw) := by
  rintro _ ⟨c, hc, rfl⟩
  have hc' : IsLocallyConstant (c : G → M) := hc
  refine ⟨restrictCocycles1 ρ Dw c, ?_, rfl⟩
  exact hc'.comp_continuous continuous_subtype_val

section
variable {O Γ VT VT' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']

theorem clsRow_of_mem (D : LatData O Γ VT VT') {T₂ : Type} [AddCommGroup T₂] [Module O T₂] (v : T₂ ≃ₗ[O] D.T')
    (f : Γ → T₂) (h : (fun g => v (f g)) ∈ Z1 D.ρTl') : clsRow D v f = Submodule.Quotient.mk ⟨_, h⟩ :=
  dite_eq_left h

end

end Formalism.RepresentationBoundsCohomology.FIN
