module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TsumThree
import Mathlib.Tactic.Lemma

@[expose] public section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.CaseA

lemma sg_eq (l h w S η : ℕ) : Sg l h w S η =
    (h:ℝ) * ((l:ℝ)⁻¹) ^ 2 + (w:ℝ) * (l:ℝ)⁻¹ + (S:ℝ) * (l:ℝ)⁻¹ + (η:ℝ) * (l:ℝ)⁻¹ +
      Real.logb l (2 * (h:ℝ)) + 1 := by
  unfold Sg
  ring

lemma logb_nn (l h : ℕ) (hl : 11 ≤ l) (h1 : 1 ≤ h) : 0 ≤ Real.logb l (2 * (h:ℝ)) := by
  apply Real.logb_nonneg
  · have : (11 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  · have : (1 : ℝ) ≤ h := by exact_mod_cast h1
    linarith

lemma sg_ge (l h w S η : ℕ) (hl : 11 ≤ l) (h1 : 1 ≤ h) :
    0 ≤ (h:ℝ) * ((l:ℝ)⁻¹) ^ 2 ∧ 0 ≤ (w:ℝ) * (l:ℝ)⁻¹ ∧ 0 ≤ (S:ℝ) * (l:ℝ)⁻¹ ∧
      0 ≤ (η:ℝ) * (l:ℝ)⁻¹ ∧ 0 ≤ Real.logb l (2 * (h:ℝ)) ∧
      Real.logb l (2 * (h:ℝ)) + 1 + (η:ℝ) * (l:ℝ)⁻¹ ≤ Sg l h w S η ∧ 1 ≤ Sg l h w S η := by
  have hlg := logb_nn l h hl h1
  have a1 : 0 ≤ (h:ℝ) * ((l:ℝ)⁻¹) ^ 2 := by positivity
  have a2 : 0 ≤ (w:ℝ) * (l:ℝ)⁻¹ := by positivity
  have a3 : 0 ≤ (S:ℝ) * (l:ℝ)⁻¹ := by positivity
  have a4 : 0 ≤ (η:ℝ) * (l:ℝ)⁻¹ := by positivity
  rw [sg_eq]
  refine ⟨a1, a2, a3, a4, hlg, by linarith, by linarith⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries.CaseA
