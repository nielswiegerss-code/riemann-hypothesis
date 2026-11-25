module

public import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
public import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHeckeFunctional
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSeriesConvergent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightContinuousPos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactStandardMaximal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbBar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftInvertibleExistsNonzeroMinor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PluckerMinorsDetermineColumnSpace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableHeightPowOfPolynomialCount
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

namespace PositivityTheory.SiegelWeilFormula.Aeis

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem eis_left_rat_w {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} (hK : IsHgt K a) {χ : Chr F E} {s₁ : ℂ} {f : G2 σ Y → ℂ}
    (hf : IsSec K χ s₁ f) (hχ : IsHecke F E χ) (t : ℝ) (Ê : ℂ → G2 σ Y → ℂ)
    (hs : ∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) :
    ∀ s : ℂ, t < s.re → ∀ γ ∈ rat2 σ Y, ∀ x, Ê s (γ * x) = Ê s x := by
  intro s' hs' γ hγ x
  exact (GlobalTheory.CompanionTheory.EisRat.law_flat hK hf s').eis_rat hχ (hs s' hs') hγ x

end PositivityTheory.SiegelWeilFormula.Aeis
