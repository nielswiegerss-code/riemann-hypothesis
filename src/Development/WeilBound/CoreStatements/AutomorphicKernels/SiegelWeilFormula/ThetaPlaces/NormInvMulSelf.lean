module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.RelReal
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.IsPureTIff

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.ThetaDictR

open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem piInf_one {w : InfinitePlace F} (τ : EmbOver E w) (x : E) : piInf τ ((1 : AF F) ⊗ₜ[F] x) = τ.1 x := by
  simp [piInf, compInf, infEmb_tmul]

theorem norm_inv_mul_self {z : ℂ} (hz : z ≠ 0) (him : z.im = 0) :
    ((‖z‖⁻¹ : ℝ) : ℂ) * z = if 0 < z.re then 1 else -1 := by
  have hz' : z = (z.re : ℂ) := Complex.ext rfl (by simp [him])
  have hn : ‖z‖ = |z.re| := by rw [hz', Complex.norm_real, Real.norm_eq_abs]; simp
  have hre : z.re ≠ 0 := fun h => hz (by rw [hz', h]; simp)
  rw [hn]
  split_ifs with hpos
  · rw [abs_of_pos hpos, hz']
    push_cast
    rw [Complex.ofReal_re]
    exact inv_mul_cancel₀ (by exact_mod_cast hre)
  · have hneg : z.re < 0 := lt_of_le_of_ne (not_lt.1 hpos) hre
    rw [abs_of_neg hneg, hz']
    push_cast
    rw [Complex.ofReal_re, inv_neg, neg_mul, inv_mul_cancel₀ (by exact_mod_cast hre)]

end PositivityTheory.SiegelWeilFormula.ThetaDictR
