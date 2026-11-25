module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeisenbergCombinationSplitPlaceDatum

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct

namespace GlobalTheory.LocMod.CombAt

theorem exists_isCombAt {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (p : Place D k) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) {S T : HSp D} (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y)
    (Ξ : Matrix Y Y' k → ℂ) : ∃ c : WO S T →₀ ℂ, p.IsCombAt ψ FS FT c Ξ := by
  by_cases h : ∃ Φ : SB (Matrix Y Y' k), Φ.1 = Ξ
  · obtain ⟨Φ, hΦ⟩ := h
    obtain ⟨O, hO, hO0⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := k) (Y := Y) (Y' := Y')
    have hne : O ≠ 0 := by
      rintro rfl
      simp at hO0
    obtain ⟨c, h1, h2⟩ := GlobalTheory.LocComb.exists_comb D k p Y Y' S T FS FT ψ hψ O Φ hne
    refine ⟨c, h1, fun Tm hT Φ₀ Φ' h₀ h' => ?_⟩
    obtain rfl : Φ' = Φ := Subtype.ext (h'.trans hΦ.symm)
    obtain rfl : Φ₀ = O := Subtype.ext (h₀.trans hO.symm)
    exact h2 Tm hT
  · exact ⟨0, by simp, fun Tm _ Φ₀ Φ _ h' => (h ⟨Φ, h'⟩).elim⟩

end GlobalTheory.LocMod.CombAt
