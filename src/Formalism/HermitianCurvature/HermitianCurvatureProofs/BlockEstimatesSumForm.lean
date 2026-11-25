module

public import Formalism.HermitianCurvature.LatticeHerglotzBound
import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

open Finset

namespace Formalism.FourierDecayAlt.P.BaseGramNonnegativity

open Formalism.FourierDecayAlt.crystallineComparison Formalism.FourierDecayAlt.TB

theorem sum_re_nonneg {α : Type} (Y : Finset α) (κ G : α → α → ℂ) (hκ : PSDOn Y κ) (hG : PSDOn Y G) :
    0 ≤ (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * G h h').re := by
  have H := (Matrix.PosSemidef.hadamard hκ hG).re_dotProduct_nonneg (fun _ => (1 : ℂ))
  simp only [dotProduct, Matrix.mulVec, Matrix.hadamard_apply, Matrix.of_apply, Pi.star_apply,
    star_one, one_mul, mul_one, RCLike.re_to_complex] at H
  convert H using 2
  rw [← Finset.sum_coe_sort Y]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [← Finset.sum_coe_sort Y]

variable {E W : Type} [Field E] (D : Data E W)

theorem baseGram_nonneg (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (w : W)
    (Y : Finset (Pt E)) (κ : Pt E → Pt E → ℂ) (hκ : PSDOn Y κ) : 0 ≤ D.N0 ε k w Y κ :=
  div_nonneg (sum_re_nonneg Y κ _ hκ (hG ε hε k w Y)) (hW w).le

theorem Wb_mono {n m : ℕ} (h : n ≤ m) : D.Wb n ⊆ D.Wb m := by
  intro x hx
  simp only [Data.Wb, Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.trans h⟩

theorem estBlockOfSumForm_ok : EstBlockOfSumForm := by
  intro E W _ D C₄ hG hW hSF ε hε i s hs hsi hir w hw hcnt hvol
  obtain ⟨Mv, hMv, θ, hθ, hb⟩ := hSF ε hε i s hs hsi hir w hw hcnt hvol
  have hsub : D.Wb (D.cnt w + s * D.K) ⊆ D.Wb (D.cnt w + (s + 1) * D.K) :=
    Wb_mono D (by nlinarith)
  have hext : ∀ g : W → ℝ, ∑ w' ∈ D.Wb (D.cnt w + (s + 1) * D.K), θ w' * g w' =
      ∑ w' ∈ D.Wb (D.cnt w + s * D.K), θ w' * g w' := by
    intro g
    symm
    refine Finset.sum_subset hsub (fun x _ hx => ?_)
    rw [hθ.2.1 x hx, zero_mul]
  refine ⟨θ, ⟨hθ.1, fun a ha => hθ.2.1 a (fun h => ha (hsub h)), ?_⟩, ?_⟩
  · have := hext (fun _ => 1)
    simp only [mul_one] at this
    rw [this, hθ.2.2]
  · intro Y hY κ hκ t₀ S hS
    have h := hb Y hY κ hκ t₀ S hS
    rw [hext]
    have hX : 0 ≤ ∑ w' ∈ D.Wb (D.cnt w + s * D.K), θ w' * D.N0 ε (i - s) w' Y κ :=
      Finset.sum_nonneg (fun w' _ => mul_nonneg (hθ.1 w') (baseGram_nonneg D hG hW hε _ _ Y κ hκ))
    exact h.trans (mul_le_mul_of_nonneg_right hMv hX)

end Formalism.FourierDecayAlt.P.BaseGramNonnegativity
