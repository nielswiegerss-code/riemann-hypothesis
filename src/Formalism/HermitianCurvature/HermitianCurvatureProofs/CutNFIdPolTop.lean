module

public import Formalism.HermitianCurvature.StatementD
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP.PolTop

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate

theorem orbital_integrand_linear {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r)
    (H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)) (a b : ℂ) (p : B.SS k r) :
    D.orbIntegrand Bs γ (fun g => a • H₁ g + b • H₂ g) p =
      a • D.orbIntegrand Bs γ H₁ p + b • D.orbIntegrand Bs γ H₂ p := by

  unfold D.orbIntegrand B.rho
  ext x
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    map_add, map_smul, smul_add]
  rw [smul_comm (B.xiTau Bs (1, 1) p) a, smul_comm (B.xiTau Bs (1, 1) p) b]

theorem orbJ_linear_of_decay : ∃ c₃ : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r)
    (w : Equiv.Perm (Fin (r + 1))) (d : Fin (r + 1) → ℂ) (A : ℝ),
    γ ∈ B.GV k r → (∀ a, d a ≠ 0) → Zhat k r Bs.z Bs.z' γ = C2.monoP w d →
    0 < Gf k r Bs.z Bs.z' γ → C6.IsRelevant Bs γ →
    c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A →
    ∀ (H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)) (cF : ℝ), 0 ≤ cF →
      AEStronglyMeasurable (D.orbIntegrand Bs γ H₁) Bs.μSS →
      AEStronglyMeasurable (D.orbIntegrand Bs γ H₂) Bs.μSS →
      (∀ p, Bs.inSS p → ‖H₁ (B.sgs p γ)‖ ≤ cF * B.gN (B.sgs p γ) ^ (-A)) →
      (∀ p, Bs.inSS p → ‖H₂ (B.sgs p γ)‖ ≤ cF * B.gN (B.sgs p γ) ^ (-A)) → ∀ a b : ℂ,
      D.orbJ Bs γ (D.muR Bs γ w) (fun g => a • H₁ g + b • H₂ g) =
        a • D.orbJ Bs γ (D.muR Bs γ w) H₁ + b • D.orbJ Bs γ (D.muR Bs γ w) H₂ := by
  obtain ⟨c₃, hc₃⟩ := Formalism.FourierDecayAlt.P.PBE.orbJ_dom
  refine ⟨c₃, ?_⟩
  intro k r Wp Wq _ _ _ _ Bs γ w d A hγ hd hZ hpos hrel hA H₁ H₂ cF hcF hm₁ hm₂ hb₁ hb₂ a b
  obtain ⟨θ, maj, hθ, hmaj, hdom⟩ := hc₃ k r Wp Wq Bs γ w d A hγ hd hZ hpos hA
  have hG : Formalism.FourierDecayAlt.P.Dx2.Rad.Good Bs γ w d := ⟨Formalism.FourierDecayAlt.P.Dx2.Rad.exists_rho Bs hγ hpos hd hZ,
    Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj Bs hγ hpos hd hZ, fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.u_lstg Bs hγ hpos hd hZ hρ⟩
  have hR := Formalism.FourierDecayAlt.P.Dx2.Rad.haar_good Bs hγ hd hG
  have hInt : ∀ (G : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), 0 ≤ c →
      AEStronglyMeasurable (D.orbIntegrand Bs γ G) Bs.μSS →
      (∀ p, Bs.inSS p → ‖G (B.sgs p γ)‖ ≤ c * B.gN (B.sgs p γ) ^ (-A)) →
      Integrable (fun p => θ p • D.orbIntegrand Bs γ G p) Bs.μSS := fun G c hc hGm hGb =>
    Integrable.mono' (hmaj.const_mul c) (hθ.1.aestronglyMeasurable.smul hGm) (hdom G c hc hGb)
  have hEq : ∀ (G : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), 0 ≤ c →
      AEStronglyMeasurable (D.orbIntegrand Bs γ G) Bs.μSS →
      (∀ p, Bs.inSS p → ‖G (B.sgs p γ)‖ ≤ c * B.gN (B.sgs p γ) ^ (-A)) →
      D.orbJ Bs γ (D.muR Bs γ w) G = ∫ p, θ p • D.orbIntegrand Bs γ G p ∂Bs.μSS := by
    intro G c hc hGm hGb
    have hex : ∃ θ', D.IsNormCut Bs γ (D.muR Bs γ w) θ' ∧
        Integrable (fun p => θ' p • D.orbIntegrand Bs γ G p) Bs.μSS := ⟨θ, hθ, hInt G c hc hGm hGb⟩
    unfold D.orbJ
    rw [dite_eq_left hex]
    exact Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq Bs γ (D.muR Bs γ w) hrel hR G _ θ hex.choose_spec.1 hθ
      hex.choose_spec.2 (hInt G c hc hGm hGb)
  have hlin : D.orbIntegrand Bs γ (fun g => a • H₁ g + b • H₂ g) =
      fun p => a • D.orbIntegrand Bs γ H₁ p + b • D.orbIntegrand Bs γ H₂ p :=
    funext fun p => orbital_integrand_linear Bs γ H₁ H₂ a b p
  have hm : AEStronglyMeasurable (D.orbIntegrand Bs γ (fun g => a • H₁ g + b • H₂ g)) Bs.μSS := by
    rw [hlin]
    exact (hm₁.const_smul a).add (hm₂.const_smul b)
  have hc' : 0 ≤ (‖a‖ + ‖b‖) * cF := mul_nonneg (by positivity) hcF
  have hb : ∀ p, Bs.inSS p → ‖a • H₁ (B.sgs p γ) + b • H₂ (B.sgs p γ)‖ ≤
      (‖a‖ + ‖b‖) * cF * B.gN (B.sgs p γ) ^ (-A) := by
    intro p hp
    have h1 := hb₁ p hp
    have h2 := hb₂ p hp
    calc ‖a • H₁ (B.sgs p γ) + b • H₂ (B.sgs p γ)‖ ≤ ‖a‖ * ‖H₁ (B.sgs p γ)‖ + ‖b‖ * ‖H₂ (B.sgs p γ)‖ := by
          refine (norm_add_le _ _).trans (le_of_eq ?_)
          rw [norm_smul, norm_smul]
      _ ≤ ‖a‖ * (cF * B.gN (B.sgs p γ) ^ (-A)) + ‖b‖ * (cF * B.gN (B.sgs p γ) ^ (-A)) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
      _ = (‖a‖ + ‖b‖) * cF * B.gN (B.sgs p γ) ^ (-A) := by ring
  have i₁ := hInt H₁ cF hcF hm₁ hb₁
  have i₂ := hInt H₂ cF hcF hm₂ hb₂
  rw [hEq _ _ hc' hm hb, hEq H₁ cF hcF hm₁ hb₁, hEq H₂ cF hcF hm₂ hb₂, hlin]
  have e : (fun p => θ p • (a • D.orbIntegrand Bs γ H₁ p + b • D.orbIntegrand Bs γ H₂ p)) =
      fun p => a • (θ p • D.orbIntegrand Bs γ H₁ p) + b • (θ p • D.orbIntegrand Bs γ H₂ p) := by
    funext p
    rw [smul_add, smul_comm (θ p) a, smul_comm (θ p) b]
  have j₁ : Integrable (fun p => a • (θ p • D.orbIntegrand Bs γ H₁ p)) Bs.μSS := i₁.smul a
  have j₂ : Integrable (fun p => b • (θ p • D.orbIntegrand Bs γ H₂ p)) Bs.μSS := i₂.smul b
  rw [e, integral_add j₁ j₂, integral_smul, integral_smul]

theorem vector_valued_orbital_linear : ∃ c₃ : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (q : C.LPt) (A : ℝ),
    c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A →
    ∀ (H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)) (cF : ℝ), 0 ≤ cF →
      ContinuousOn H₁ (B.GPos Bs) → ContinuousOn H₂ (B.GPos Bs) →
      (∀ g ∈ B.GPos Bs, ‖H₁ g‖ ≤ cF * B.gN g ^ (-A)) → (∀ g ∈ B.GPos Bs, ‖H₂ g‖ ≤ cF * B.gN g ^ (-A)) →
      ∀ a b : ℂ, D.vecV Bs ν' m₀ (fun g => a • H₁ g + b • H₂ g) q =
        a • D.vecV Bs ν' m₀ H₁ q + b • D.vecV Bs ν' m₀ H₂ q := by
  obtain ⟨c₃, hc₃⟩ := orbJ_linear_of_decay
  refine ⟨c₃, ?_⟩
  intro k r Wp Wq _ _ _ _ Bs ν' m₀ q A hA H₁ H₂ cF hcF hc₁ hc₂ hb₁ hb₂ a b
  unfold D.vecV
  by_cases h : D.IsLocPt q (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q
  · simp only [dite_eq_left h]
    by_cases h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN q (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ
    · simp only [dite_eq_left h']
      have hγ := h'.choose_spec.1
      have hZ := h'.choose_spec.2.1
      have hGq := Formalism.FourierDecayAlt.P.ptG_spec k r Bs.z Bs.z' q h'.choose h.1 hZ
      have hpos : 0 < Gf k r Bs.z Bs.z' h'.choose := hGq ▸ h.2
      obtain ⟨hmono, hd⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' q (r + 1) h.1.2 h.1.1
      have hrel := Formalism.FourierDecayAlt.P.relevant_points_holds k r Wp Wq Bs q h'.choose h.1 hγ hZ
      have horb : ∀ p, Bs.inSS p → B.sgs p h'.choose ∈ B.GPos Bs := fun p hp =>
        ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ, by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]; exact hpos⟩
      exact hc₃ k r Wp Wq Bs h'.choose _ _ A hγ hd (hZ.trans hmono) hpos hrel hA H₁ H₂ cF hcF
        (Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs horb hc₁) (Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs horb hc₂)
        (fun p hp => hb₁ _ (horb p hp)) (fun p hp => hb₂ _ (horb p hp)) a b
    · simp only [dite_eq_right h']
      simp
  · simp only [dite_eq_right h]
    simp

end Formalism.FourierDecayAlt.P.CutBP.PolTop
