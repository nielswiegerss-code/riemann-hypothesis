module

import all Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrFwd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr
open UpperTheory.V.Lit.Geo

section

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem sand_comp (g h : GL (Fin a) (Cinf E)) (v : HV E a) : sand g (sand h v) = sand (g * h) v := by
  rw [map_mul]; rfl

private theorem unitary_of_eq {g h : GL (Fin a) (Cinf E)} (e : sand g (hOne E a) = sand h (hOne E a)) :
    ∃ k : Kinf E a, h = g * Unitary.toUnits k := by
  apply _root_.UpperTheory.V.Lit.Dr.exists_unitary <;> assumption

private theorem hv_adHerm (k : Kinf E a) (X : Herm E a) : hv (adHerm k X) = sand (Unitary.toUnits k) (hv X) := rfl

end

theorem UpperTheory.V.Lit.Geo.fieldDef :
    FieldDef := by
  classical
  intro E _ _ _ a U Y C hY
  refine ⟨fun s p => if h : p ∈ cone E a then
    sand h.choose (hv (Y (infGL E a h.choose * finGL E a s.out))) else 0, fun g x => ?_⟩
  have hp : sand g (hOne E a) ∈ cone E a := ⟨g, rfl⟩
  obtain ⟨k, hk⟩ := unitary_of_eq hp.choose_spec.symm
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U x
  beta_reduce
  rw [dite_eq_left hp, hk, hu, map_mul (finGL E a), ← mul_assoc, hY.lev _ u.2, ← sand_comp, ← hv_adHerm,
    map_mul (infGL E a), mul_assoc, infGL_comm, ← mul_assoc, hY.cpt]
