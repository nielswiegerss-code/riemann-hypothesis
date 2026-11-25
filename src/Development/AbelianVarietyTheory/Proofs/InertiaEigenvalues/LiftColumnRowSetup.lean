module

public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LocalErrorBoundPlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfCrystallineLift
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.LiftExpSplit

open Module

variable {D : D7}

theorem lift_of_window (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hC : C.IsGood)
    (hur : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i)) (hl : D.nd.l i ≠ 2) {ι : Type} {k : ℕ}
    (Ms : ι → Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥C.LL.1)
    (hc : ∀ x v, Continuous fun g => (Ms x g).mulVec v)
    (hF : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAt (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 ↥(OL C.LL)) (M h : ℕ)
    (hcr : ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Ms x)))
    (hS : ∀ x τ, JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (Ms x)) τ (Set.Icc (-(M : ℤ)) h))
    (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) {CA CB CK : ℝ} (hCA : 0 ≤ CA)
    (h54 : Formalism.MainNotions.LiftingTheory.LiftTheoremAllCases D HW F CA CB CK) (e' : ℕ)
    (he : CA * (1 + ((M + h : ℕ) : ℝ) / (D.nd.l i : ℝ) +
      (1 + Real.logb (D.nd.l i) (((M + h : ℕ) : ℝ) + 1))) ≤ (e' : ℝ)) :
    LiftAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) (fun x : ι => ⇑(Ms x)) e' := by
  have hg : Good (D.nbr i w hw).Kw 1 C.LL := hC.good_one hl (le_trans (le_inf le_rfl hur) le_sup_left)
  have hA := caseA_of_unram (D.loc (D.nd.l i)) (HW (D.nd.l i)) hg hur hl
  intro V1 _ _ _ _ _ _ _ _ _ _ _ ρ1 L1 hc1 hs1 V2 _ _ _ _ _ _ _ _ _ _ _ ρ2 L2 hc2 hs2 F hF'
  let T₁ : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
    { V := V1, ρ := ρ1, cont := hc1, L := L1 }
  let T₂ : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
    { V := V2, ρ := ρ2, cont := hc2, L := L2 }
  obtain ⟨hcr1, hj1⟩ := subquot_crys (PD := Br.PD D.loc D.nbr i w hw) Ms hc hF
    (S := fun _ => Set.Icc (-(M : ℤ)) h) hcr hS T₁ hs1
  obtain ⟨hcr2, -⟩ := subquot_crys (PD := Br.PD D.loc D.nbr i w hw) Ms hc hF
    (S := fun _ => Set.Icc (-(M : ℤ)) h) hcr hS T₂ hs2
  have hJ : Formalism.MainNotions.LiftingTheory.JumpsLet ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hg) T₁
      (fun _ => M) (fun _ => h) := fun _ τ _ => hj1 τ
  have h1 := h54.1 (D.nd.l i) (D.nbr i w hw).Kw 1 C.LL hg hA T₁ T₂ F (fun _ => M) (fun _ => h)
    ⟨hcr1, hcr2, hF'⟩ hJ
  have h2 := (h54.2.2.2.1 (D.nd.l i) (D.nbr i w hw).Kw 1 C.LL hg T₁ (fun _ => M) (fun _ => h) hcr1 hJ).1 hA
  refine LiftF_mono _ F ?_ h1
  have hp : (((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p : ℝ) = (D.nd.l i : ℝ) := by
    rw [(D.loc (D.nd.l i)).PD_p]
  have hl1 : (1 : ℝ) < (D.nd.l i : ℝ) := by exact_mod_cast (D.nd.lPrime i).out.one_lt
  have hH : ((Formalism.MainNotions.LiftingTheory.Hmax (Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) (fun _ => M)
      (fun _ => h) : ℕ) : ℝ) ≤ ((M + h : ℕ) : ℝ) := by exact_mod_cast Hmax_const_le _ M h
  rw [hp] at h2
  have h3 : CA * (1 + ((Formalism.MainNotions.LiftingTheory.Hmax (Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) (fun _ => M)
      (fun _ => h) : ℕ) : ℝ) / (D.nd.l i : ℝ) + (1 + Real.logb (D.nd.l i)
        (((Formalism.MainNotions.LiftingTheory.Hmax (Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) (fun _ => M)
      (fun _ => h) : ℕ) : ℝ) + 1))) ≤ CA * (1 + ((M + h : ℕ) : ℝ) / (D.nd.l i : ℝ) +
      (1 + Real.logb (D.nd.l i) (((M + h : ℕ) : ℝ) + 1))) := by
    apply mul_le_mul_of_nonneg_left _ hCA
    have ha := div_le_div_of_nonneg_right hH (le_of_lt (lt_trans zero_lt_one hl1))
    have hb := Real.logb_le_logb_of_le hl1 (by positivity) (add_le_add_left hH 1)
    linarith
  exact_mod_cast (h2.trans (h3.trans he))

theorem shape_le_eA (L : SizeData₂ D) (CA : ℝ) (l : ℕ) :
    CA * (1 + ((Formalism.MainNotions.N.hN L + Formalism.MainNotions.N.hN L : ℕ) : ℝ) / (l : ℝ) +
      (1 + Real.logb l (((Formalism.MainNotions.N.hN L + Formalism.MainNotions.N.hN L : ℕ) : ℝ) + 1))) ≤ (eA L CA l : ℝ) := by
  unfold eA
  exact Nat.le_ceil _

theorem mem_window (L : SizeData₂ D) (a : ℤ) (ha : |(a : ℝ)| ≤ Formalism.MainNotions.TwistedPlaces.hB L) :
    a ∈ Set.Icc (-(Formalism.MainNotions.N.hN L : ℤ)) (Formalism.MainNotions.N.hN L) := by
  have h1 : a.natAbs ≤ Formalism.MainNotions.N.hN L := by
    unfold Formalism.MainNotions.N.hN
    apply Nat.le_floor
    rw [Nat.cast_natAbs, Int.cast_abs]
    exact ha
  constructor <;> omega

end GlobalTheory.LiftExpSplit
