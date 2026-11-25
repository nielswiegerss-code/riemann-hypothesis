module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChart
import Mathlib.Topology.Compactification.OnePoint.Basic

@[expose] public section

namespace ReciprocityTheory.AnForm.R

open MvPolynomial OnePoint Filter Topology

theorem ptIdeal_eq_span {n : ℕ} (p : Fin n → ℂ) :
    ptIdeal p = Ideal.span (Set.range fun i => X i - C (p i)) := by
  apply le_antisymm
  · intro f hf
    have h0 : eval p f = 0 := hf
    simpa [h0] using _root_.Bl.general_b_fact_left_more.goal1 p f
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    show eval p (X i - C (p i)) = 0
    simp

end ReciprocityTheory.AnForm.R
