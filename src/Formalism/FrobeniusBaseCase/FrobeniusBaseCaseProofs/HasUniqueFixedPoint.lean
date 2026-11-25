module

public import Formalism.FrobeniusBaseCase.Statement
import Mathlib.Tactic.TypeStar
public import Mathlib.Algebra.Ring.GeomSum

@[expose] public section

open MvPowerSeries

namespace Formalism.BaseCaseIdentities

open Classical

variable {k : Type*} [Field k] {Z : Type*} {C : Type*}

theorem OrdGE.mono {a b : ℕ} {f : MvPowerSeries Z k} (h : a ≤ b) (hf : OrdGE b f) : OrdGE a f := by
  intro A hA
  exact hf A (lt_of_lt_of_le hA h)

theorem OrdGE.zero {n : ℕ} : OrdGE n (0 : MvPowerSeries Z k) := by
  intro A _
  simp

theorem OrdGE.sub {n : ℕ} {f g : MvPowerSeries Z k} (hf : OrdGE n f) (hg : OrdGE n g) :
    OrdGE n (f - g) := by
  intro A hA
  rw [map_sub, hf A hA, hg A hA, sub_zero]

theorem OrdGE.sum {ι : Type*} {n : ℕ} (s : Finset ι) {f : ι → MvPowerSeries Z k}
    (hf : ∀ i ∈ s, OrdGE n (f i)) : OrdGE n (∑ i ∈ s, f i) := by
  intro A hA

  rw [map_sum]
  exact Finset.sum_eq_zero fun i hi => hf i hi A hA

theorem OrdGE.mul {a b : ℕ} {f g : MvPowerSeries Z k} (hf : OrdGE a f) (hg : OrdGE b g) :
    OrdGE (a + b) (f * g) := by
  intro A hA
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp' : p.1 + p.2 = A := by simpa using hp
  have hd : p.1.degree + p.2.degree = A.degree := by
    rw [← hp', map_add (f := _)]
  by_cases h1 : p.1.degree < a
  · rw [hf _ h1, zero_mul]
  · rw [hg _ (by omega), mul_zero]

theorem OrdGE.C_mul {n : ℕ} {f : MvPowerSeries Z k} (x : k) (hf : OrdGE n f) :
    OrdGE n (MvPowerSeries.C x * f) := by
  intro A hA
  rw [coeff_C_mul, hf A hA, mul_zero]

theorem OrdGE.pow {f : MvPowerSeries Z k} (hf : OrdGE 1 f) (n : ℕ) : OrdGE n (f ^ n) := by
  induction n with
  | zero => intro A hA; exact absurd hA (Nat.not_lt_zero _)
  | succ n ih => rw [pow_succ]; exact ih.mul hf

theorem OrdGE.X (d : Z) : OrdGE 1 (X d : MvPowerSeries Z k) := by
  intro A hA
  rw [coeff_X]
  split_ifs with h
  · subst h
    simp at hA
  · rfl

theorem OrdGE.pow_sub_pow {f g : MvPowerSeries Z k} {n : ℕ} (hf : OrdGE 1 f) (hg : OrdGE 1 g)
    (hfg : OrdGE (n + 1) (f - g)) {N : ℕ} (hN : 1 ≤ N) : OrdGE (n + N) (f ^ N - g ^ N) := by
  rw [← geom_sum₂_mul]
  have hs : OrdGE (N - 1) (∑ i ∈ Finset.range N, f ^ i * g ^ (N - 1 - i)) := by
    refine OrdGE.sum _ fun i hi => ?_
    rw [Finset.mem_range] at hi
    exact OrdGE.mono (show N - 1 ≤ i + (N - 1 - i) by omega) ((hf.pow i).mul (hg.pow (N - 1 - i)))
  exact OrdGE.mono (by omega) (hs.mul hfg)

namespace Data

variable [Fintype Z] [Fintype C] (D : Data k Z C)

end Data

end Formalism.BaseCaseIdentities
