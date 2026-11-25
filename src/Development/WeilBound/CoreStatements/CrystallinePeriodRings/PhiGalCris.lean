module

public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.ExistsMapEqOfPowMul

@[expose] public section

namespace PositivityTheory.LocInh

open GroundTheory.PAdicHodge Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GaloisCommutant

section Abstract

variable {A B E : Type} [CommRing A] [CommRing B] [CommRing E] {a t : A} {f : A →+* B}

theorem comm_equiv (hf : IsFrac f a t) (ι : B →+* E) (s : B →+* B) (d : E ≃+* E)
    (e : ∀ x, ι (s (f x)) = d (ι (f x))) (b : B) : ι (s b) = d (ι b) :=
  RingHom.congr_fun (hf.hom_ext (g := ι.comp s) (h := (d : E →+* E).comp ι) e) b

end Abstract

variable {l : ℕ} [Fact l.Prime]

theorem σD_eq (g : GQ l) : Per6.σD g = galBdRField (Per6.toBot g) := rfl

theorem σD_algebraMap (g : GQ l) (y : Per6.BdRp l) :
    Per6.σD g (algebraMap (Per6.BdRp l) (Per6.BdR l) y) =
      algebraMap (Per6.BdRp l) (Per6.BdR l) (Per6.toBot g • y) := by
  rw [σD_eq, galBdRField_algebraMap]

theorem cD_galCris (g : GQ l) (x : ACris.ACris ℂ_[l] l) :
    cD l (ACris.galCris (Per6.toBot g) x) = Per6.σD g (cD l x) := by
  rw [cD_apply, cD_apply, σD_algebraMap, ← ACris.gal_smul_def, ACris.iota_gal_smul]

theorem ιCD_σB_aux (g : GQ l) (b : Per6.Bcris l) : ιCD l (Per6.σB g b) = Per6.σD g (ιCD l b) :=
  comm_equiv (cB_isFrac l) _ _ _ (fun x =>
    ((congrArg (ιCD l) (σB_cB g x)).trans (ιCD_cB _)).trans
      ((cD_galCris g x).trans (congrArg (Per6.σD g) (ιCD_cB x).symm))) b

theorem oD_apply (x : Om l) :
    oD l x = algebraMap (Per6.BdRp l) (Per6.BdR l) (algClToBdR l x) := rfl

theorem coe_χQ (g : GQ l) :
    ((χQ l g : ℚ_[l]ˣ) : ℚ_[l]) = ((cycloChar ⊥ (Per6.toBot g) : ℤ_[l]) : ℚ_[l]) := rfl

theorem cD_χA (g : GQ l) : cD l (Per6.χA (Per6.toBot g)) =
    oD l (algebraMap ℚ_[l] (Om l) ((χQ l g : ℚ_[l]ˣ) : ℚ_[l])) := by
  rw [cD_apply, Per6.χA, ACris.iota_padicInt, oD_apply, AlgHom.commutes, coe_χQ]

theorem cB_χA (g : GQ l) : Per6.cB l (Per6.χA (Per6.toBot g)) = qB l ((χQ l g : ℚ_[l]ˣ) : ℚ_[l]) :=
  ιCD_injective (((ιCD_cB _).trans (cD_χA g)).trans (ιCD_qB _).symm)

theorem tB_eq : tB l = Per6.cB l (Per6.tA l) := rfl

end GaloisCommutant

open GaloisCommutant

variable {l : ℕ} [Fact l.Prime]

theorem σD_oD (g : GQ l) (x : Om l) : Per6.σD g (oD l x) = oD l (g x) := by
  rw [oD_apply, oD_apply, σD_algebraMap, gal_smul_algClToBdR]
  rfl

theorem σB_tB (g : GQ l) : Per6.σB g (tB l) = qB l ((χQ l g : ℚ_[l]ˣ) : ℚ_[l]) * tB l := by
  rw [tB_eq, σB_cB, Per6.galCris_tA, map_mul, cB_χA]

end PositivityTheory.LocInh
