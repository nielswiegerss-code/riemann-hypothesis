module

public import Formalism.HermitianCurvature.StatementTBB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Mathlib.Algebra.Order.Star.Real

@[expose] public section

namespace Formalism.FourierDecayAlt.P.TBBx3

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem vecCutAt_of_one (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hχ : ∀ x, 1 ≤ x → χ x = 1) : TBB.VecCutAt p χ F := by
  intro ε hε γ hγ hle
  have hle0 : ε ≤ D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r γ := hle
  unfold KB.Pl.V D.vecV
  split_ifs with h h'
  · rw [Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_cutF]
    have hG := Formalism.FourierDecayAlt.P.ptG_spec P.k P.r p.T.base.z p.T.base.z' γ h'.choose hγ h'.choose_spec.2.1
    have hle' : ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' h'.choose := hG ▸ hle0
    rw [hχ _ ((one_le_div hε).mpr hle'), Complex.ofReal_one, one_smul]
  · rfl
  · rfl

theorem hsInner_self_re_nonneg (A : Wq →L[ℂ] Wp) : 0 ≤ (B.hsInner A A).re := by
  unfold B.hsInner
  have h := inner_self_nonneg (𝕜 := ℂ) (x := B.hsVec A)
  simpa using h

theorem rr_top_re_nonneg (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (i : ℕ) (w : List C.Letter)
    (h : C.LPt) (hi : P.r < i) : 0 ≤ (p.RR F i w h h).re := by
  unfold KB.Pl.RR D.RRplace
  by_cases h1 : D.IsLocPt h i ∧ D.IsLocPt h i
  · rw [dite_eq_left h1, dite_eq_right (by omega)]
    by_cases h2 : i = P.r + 1
    · rw [ite_eq_left h2]
      by_cases h3 : w = []
      · rw [ite_eq_left h3]
        exact hsInner_self_re_nonneg _
      · rw [ite_eq_right h3]
        unfold Top.topOf
        rw [Complex.re_sum]
        refine Finset.sum_nonneg fun e _ => ?_
        rw [Complex.re_sum]
        refine Finset.sum_nonneg fun ρ _ => ?_
        rw [Complex.re_ofReal_mul]
        exact mul_nonneg (mul_self_nonneg _) (hsInner_self_re_nonneg _)
    · rw [ite_eq_right h2]
      simp
  · rw [dite_eq_right h1]
    simp

theorem posAt_of_forms (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ)
    (hnn : ∀ y, 0 ≤ nn y)
    (hform : ∀ (j : ℕ) (w : List C.Letter) (h : C.LPt), j ≤ P.r → TBB.AdmW P p.l0 Y w → w.length ≤ N →
      0 ≤ (p.RR F j w h h).re) : TBB.PosAt p nn F Y N := by
  intro i w h hw hN
  unfold TBB.Ew TBB.NP
  rw [Complex.re_ofReal_mul]
  apply mul_nonneg
  · apply div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    unfold TBB.normC
    apply List.prod_nonneg
    intro a ha
    rw [List.mem_map] at ha
    obtain ⟨l, _, rfl⟩ := ha
    exact hnn _
  · by_cases hi : i ≤ P.r
    · exact hform i w h hi hw hN
    · exact rr_top_re_nonneg p F i w h (by omega)

theorem ew_zero_nil (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) :
    TBB.Ew p nn G 0 w [] = (p.RR G 0 w [] []).re / TBB.normC nn w := by
  have h1 : ∀ TT : ℝ, TBB.nPt P.k P.r TT [] = 1 := fun TT => by simp [TBB.nPt, C.nAux]
  unfold TBB.Ew TBB.NP
  simp only [h1, Real.sqrt_one, one_mul]
  rw [Complex.re_ofReal_mul, one_div, inv_mul_eq_div]

theorem limZeroAt_of_limits (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Y : Finset ℝ) (N : ℕ) (κ₀ : ℝ)
    (hE : ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∃ sz : ℝ, 0 ≤ sz ∧ sz ≤ TBB.normC nn w ∧
      Tendsto (fun ε : ℝ => (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re) (𝓝[>] 0)
        (𝓝 (sz * (B.beta p.T.base F F).re)))
    (hB : ENNReal.ofReal (B.beta p.T.base F F).re ≤ ENNReal.ofReal κ₀ * TBB.jN2 p F) :
    TBB.LimZeroAt p nn χ F Y N κ₀ := by
  intro w hw hN
  obtain ⟨sz, hsz0, hszn, hlim⟩ := hE w hw hN
  have hEw : ∀ ε, TBB.Ew p nn (D.cutF p.T.base χ F ε) 0 w [] =
      (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re / TBB.normC nn w := fun ε => ew_zero_nil p nn _ w
  have hlim2 : Tendsto (fun ε => ENNReal.ofReal (TBB.Ew p nn (D.cutF p.T.base χ F ε) 0 w [])) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (sz * (B.beta p.T.base F F).re / TBB.normC nn w))) := by
    simp only [hEw]
    exact ENNReal.tendsto_ofReal (hlim.div_const _)
  rw [hlim2.limsup_eq]
  refine le_trans ?_ hB
  rw [ENNReal.ofReal_le_ofReal_iff']
  have hn0 : 0 ≤ TBB.normC nn w := le_trans hsz0 hszn
  by_cases hb : 0 ≤ (B.beta p.T.base F F).re
  · left
    rcases hn0.lt_or_eq with hpos | hzero
    · rw [div_le_iff₀ hpos]
      calc sz * (B.beta p.T.base F F).re ≤ TBB.normC nn w * (B.beta p.T.base F F).re :=
            mul_le_mul_of_nonneg_right hszn hb
        _ = (B.beta p.T.base F F).re * TBB.normC nn w := mul_comm _ _
    · rw [← hzero, div_zero]
      exact hb
  · right
    push Not at hb
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hsz0 hb.le) hn0

end Formalism.FourierDecayAlt.P.TBBx3
