module

public import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.GammaEqDpow

@[expose] public section

open GroundTheory.PAdicHodge
namespace Cmp6
variable (l : ℕ) [Fact l.Prime]

theorem tiltMap_eq : Reformulated.AutPerF.Tilt.map l (e l).toRingHom = Formalism.Per6.tiltMap l := by
  refine RingHom.ext fun x => Reformulated.AutPerF.Tilt.ext fun n => ?_
  rw [Reformulated.AutPerF.Tilt.coeff_map]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  change _ = Formalism.Per6.modPEquiv l (PreTilt.coeff n x)
  rw [← ha, Ideal.quotientMap_mk]
  rfl

theorem ainfMap_eq : Reformulated.AutPerF.Ainf.map l (e l).toRingHom = Formalism.Per6.ainfMap l := by
  rw [Reformulated.AutPerF.Ainf.map, tiltMap_eq]
  rfl

theorem cA_algebraMap (a : Reformulated.AutPerF.Ainf l (OC l)) :
    cA l (algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.Acris l (OC l)) a) =
      algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) (Formalism.Per6.ainfMap l a) := by
  rw [cA_apply, Reformulated.AutPerF.Acris.map_algebraMap, ainfMap_eq]

end Cmp6
