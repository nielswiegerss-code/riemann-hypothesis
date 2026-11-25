module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.WspOrth
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.RealTrOfAll

@[expose] public section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem cf_sum {n : ℕ} (s : Finset (Wt n)) (g : Wt n → ℂ) (μ : Wt n) :
    cf (∑ x ∈ s, g x • ex x) μ = if μ ∈ s then g μ else 0 := by
  classical
  simp [cf, ex, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem UpperTheory.RealTr.chEx :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → ∀ B, ∃ c, IsCh F S B c := by
  intro n V _ _ F hF S hS hSt B
  obtain ⟨s, hs, -, -⟩ := wtDec n V F hF S hS hSt
  refine ⟨∑ μ ∈ s, trOn (wsp F μ ⊓ S) B • ex μ, fun μ => ?_⟩
  rw [cf_sum]
  split_ifs with h
  · rfl
  · rw [hs μ h, trOn_bot]
