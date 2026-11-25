module

public import Formalism.GaussJetBounds.Statement
import Mathlib.RingTheory.PiTensorProduct

@[expose] public section

open scoped BigOperators

universe u v

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

theorem asmR_dot_single {ι : Type v} (i : ι) (k : ℕ) (r : ι → ℝ) :
    dot (Finsupp.single i k) r = (k : ℝ) * r i := by
  unfold dot
  rw [Finsupp.sum_single_index (by simp)]

theorem asmR_dot_pureMon {ι : Type v} [DecidableEq ι] (l : ℕ) (i j : ι) (α β : ℕ) (r : ι → ℝ) :
    dot (pureMon l i j α β) r = (l : ℝ) ^ α * r i + (l : ℝ) ^ β * r j := by
  unfold pureMon dot
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring),
    Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  push_cast
  ring

theorem asmR_dot_add_right {ι : Type v} (n : ι →₀ ℕ) (r s : ι → ℝ) :
    dot n (fun i => r i + s i) = dot n r + dot n s := by
  unfold dot
  simp only [mul_add]
  exact Finsupp.sum_add

theorem asmR_dot_fintype {ι : Type v} [Fintype ι] (n : ι →₀ ℕ) (r : ι → ℝ) :
    dot n r = ∑ i, (n i : ℝ) * r i := by
  unfold dot
  exact Finsupp.sum_fintype _ _ (fun i => by simp)

theorem asmR_dot_nonneg {ι : Type v} (n : ι →₀ ℕ) {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i) : 0 ≤ dot n r := by
  unfold dot Finsupp.sum
  exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hr i)

theorem asmR_monoWtGe_rad {K : Type u} [NormedField K] {ι : Type v} {pi : ℝ} (h0 : 0 < pi)
    (h1 : pi ≤ 1) {r r' : ι → ℝ} (hr : ∀ i, r i ≤ r' i) {w : ℝ} {n : ι →₀ ℕ} {c : K}
    (h : MonoWtGe pi r w n c) : MonoWtGe pi r' w n c := by
  have hd : dot n r ≤ dot n r' := by
    have h := asmR_dot_add_right n r (fun i => r' i - r i)
    have hf : (fun i => r i + (r' i - r i)) = r' := by funext i; ring
    rw [hf] at h
    rw [h]
    linarith [asmR_dot_nonneg n (r := fun i => r' i - r i) (fun i => sub_nonneg.mpr (hr i))]
  unfold MonoWtGe at h ⊢
  exact h.trans (Real.rpow_le_rpow_of_exponent_ge h0 h1 (by linarith))

end Formalism.DworkPowerSeriesWeights
