module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.BasIntSmulMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.LocDefs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.CompactLocalGlobal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.AdelicLatticeToLocalLattices
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.ValNatCastLtOne

@[expose] public section

namespace PI.UnitaryGroupMassFormula.ScXuExists

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

theorem eps_idem {I : AutInst} {g r k : ℕ} {e f : Fin r → Fin I.n → I.E} (Rf : RefData I g r k e f)
    (v : HeightOneSpectrum (𝓞 I.F)) :
    PI.FinKW.psiV I v Rf.ew * PI.FinKW.psiV I v Rf.ew = PI.FinKW.psiV I v Rf.ew := by
  rw [← map_mul, Rf.ew_idem]

theorem eps_orth {I : AutInst} {g r k : ℕ} {e f : Fin r → Fin I.n → I.E} (Rf : RefData I g r k e f)
    (v : HeightOneSpectrum (𝓞 I.F)) :
    PI.FinKW.psiV I v Rf.ew * PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) = 0 := by
  rw [← PI.UnitaryGroupMassFormula.AdIndexEq.psiV_sigR, ← map_mul]
  have h := Rf.ew_orth
  have h' : Rf.ew * Formalism.UG.sigR I.cm.sig (Af I.F) Rf.ew = 0 := h
  rw [h', map_zero]

theorem incl_mem_Lf (I : AutInst) (l : Fin I.n → I.E) (hl : l ∈ I.L) :
    (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (l i)) ∈ I.Lf :=
  Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩

theorem vecV_incl (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (l : Fin I.n → I.E) :
    PI.FinKW.vecV I v (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (l i)) =
      Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) l := by
  funext i
  simp only [PI.FinKW.vecV, PI.FinKW.LocTo.psiV_inclE]
  rfl

theorem full_loc {I : AutInst} {g r k : ℕ} {e f : Fin r → Fin I.n → I.E} (Rf : RefData I g r k e f)
    (v : HeightOneSpectrum (𝓞 I.F)) (x : Fin I.n → RV I v)
    (hx : x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))) :
    ∃ w ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
      (1 - PI.FinKW.psiV I v Rf.ew - PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew)) • x =
        (g : RV I v) • w := by
  set c := (1 - PI.FinKW.psiV I v Rf.ew - PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew)) with hc
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    have hy := Rf.ew_full _ (incl_mem_Lf I l hl)
    obtain ⟨w, hw, hw'⟩ := vecV_mL I v g _ hy
    refine ⟨w, hw, ?_⟩
    rw [← hw', vecV_smul', vecV_incl, map_sub, map_sub, map_one]
    have : PI.FinKW.psiV I v (sigA I Rf.ew) = PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) :=
      PI.UnitaryGroupMassFormula.AdIndexEq.psiV_sigR I v Rf.ew
    rw [this]
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w1, hw1, h1⟩ := hx
    obtain ⟨w2, hw2, h2⟩ := hy
    exact ⟨w1 + w2, Submodule.add_mem _ hw1 hw2, by rw [smul_add, h1, h2, smul_add]⟩
  | smul o x _ hx =>
    obtain ⟨w, hw, h⟩ := hx
    refine ⟨o • w, Submodule.smul_mem _ o hw, ?_⟩
    rw [PI.FinKW.LocTo.ov_smul_vec, PI.FinKW.LocTo.ov_smul_vec, smul_comm, h, smul_comm]

theorem latLoc_fg (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    (Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))).FG :=
  PI.OmLocU.basLat_fg v I.L (Submodule.IsLattice.of_fg I.E I.L_fg)

end PI.UnitaryGroupMassFormula.ScXuExists
