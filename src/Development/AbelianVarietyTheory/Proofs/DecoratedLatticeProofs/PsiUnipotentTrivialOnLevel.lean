module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FstACoordOfInfPart
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ActsLinOfSplitLin

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl GlobalTheory.FinPlLoc Filter Topology
open scoped TensorProduct

namespace GlobalTheory.FinPl.PsiUnit

variable {D : D7}


open Formalism.IndefR.Fin.LevelGroupLemmas in
theorem char_eq_one_of_local (ψ : AddChar (AF D.host.F) ℂ) (hψ : Continuous ψ) (t : AF D.host.F)
    (ht : fstA D.host.F t = 0) (h : ∀ v : Pl D, ψ (pairA D.host.F 0 (ePl D (· = v)) * t) = 1) : ψ t = 1 := by
  classical
  have h1 : ∀ A : Finset (Pl D), ψ (idemS A * t) = 1 := by
    intro A
    induction A using Finset.induction_on with
    | empty => rw [idemS_empty, zero_mul, AddChar.map_zero_eq_one]
    | insert v A hv ih =>
      have e : idemS (insert v A) = idemS A + pairA D.host.F 0 (ePl D (· = v)) := by
        unfold idemS
        rw [← pairA_add]
        congr 1
        refine RestrictedProduct.ext _ _ fun w => ?_
        change evalV D.host.F w (sglS (insert v A)) = evalV D.host.F w (sglS A + ePl D (· = v))
        rw [map_add (f := _), evalV_sglS, evalV_sglS, evalV_ePl]
        by_cases hw : w = v
        · subst hw; simp [hv]
        · simp [hw]
      rw [e, add_mul, AddChar.map_add_eq_mul, ih, h, one_mul]
  have h2 := (hψ.tendsto 0).comp (tendsto_AF t ht)
  rw [AddChar.map_zero_eq_one] at h2
  refine tendsto_nhds_unique tendsto_const_nhds (h2.congr fun A => ?_)
  have e : t = idemS A * t + (1 - idemS A) * t := by ring
  change ψ ((1 - idemS A) * t) = ψ t
  conv_rhs => rw [e, AddChar.map_add_eq_mul, h1, one_mul]

theorem trace_idem (Q : Pl D → Prop) (s : AE D) : Algebra.trace (AF D.host.F) (AE D) (idem D Q * s) =
    pairA D.host.F 0 (ePl D Q) * Algebra.trace (AF D.host.F) (AE D) s := by
  rw [← smul_eq_mul (pairA D.host.F 0 (ePl D Q)), ← map_smul, Algebra.smul_def]
  rfl

theorem psiE_eq_one_of_local (ψ : AddChar (AF D.host.F) ℂ) (hψ : Continuous ψ) {P : Pl D → Prop} {s : AE D}
    (hs : s ∈ idAt D P) (h : ∀ v, P v → psiE ψ (idem D (· = v) * s) = 1) : psiE ψ s = 1 := by
  refine char_eq_one_of_local ψ hψ _ ?_ fun v => ?_
  · rw [← (mem_idAt_iff P s).1 hs, trace_idem, map_mul]
    exact zero_mul _
  · rw [← trace_idem]
    by_cases hv : P v
    · exact h v hv
    · have h0 : idem D (· = v) * s = 0 := by
        refine (mem_idOff_iff _ s).1 ((Submodule.mem_iInf _).2 fun w => RingHom.mem_ker.2 ?_)
        exact compAt_of_idAt hs (by rw [w.2]; exact hv)
      rw [h0]
      exact psiE_zero ψ

theorem latV_mono {S : HSp D} {L : Lat S} {P : Pl D → Prop} {v : Pl D} (hv : P v) : latV S L (· = v) ≤ latV S L P := by
  refine AddSubgroup.closure_mono ?_
  rintro y ⟨α, h1, h2, h3⟩
  exact ⟨α, h1, fun w hw => h2 w fun e => hw (e ▸ hv), h3⟩

theorem mulVec_colMul {l m n : ℕ} (A : Mx D l m) (x : Mx D m n) (i : Fin n) (a : AE D) :
    A *ᵥ colMul x i a = colMul (A ⬝ x) i a := by
  funext k
  simp only [Matrix.mulVec, dotProduct, colMul, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.FinPl.PsiUnit
