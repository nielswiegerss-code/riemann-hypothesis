module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.ThetaLifts.LatticeBasics.BoxFinB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.EqZeroOfPiInf
public import Development.WeilBound.ThetaLifts.LatticeBasics.ExistsIsGauss
import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactIntV
import Mathlib.Tactic.Linter.Style

@[expose] public section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable (d : SD σ)

variable {d}

theorem cA_incM {p q : Type} (N : Matrix p q E) : (incM F N).map (cA σ) = incM F (N.map σ) := by
  ext i j
  simp only [incM, Matrix.map_apply, inclR]
  show cA σ (Algebra.TensorProduct.includeRight (N i j)) = Algebra.TensorProduct.includeRight (σ (N i j))
  simp [cA, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]

theorem incM_mul' {p q r : Type} [Fintype q] (N : Matrix p q E) (N' : Matrix q r E) :
    incM F (N * N') = incM F N * incM F N' := Matrix.map_mul (f := inclR (F := F) (AF F))

theorem incM_transpose {p q : Type} (N : Matrix p q E) : (incM F N)ᵀ = incM F Nᵀ := rfl

theorem map_cA_mul {p q r : Type} [Fintype q] (A : Matrix p q (AE F E)) (B : Matrix q r (AE F E)) :
    (A * B).map (cA σ) = A.map (cA σ) * B.map (cA σ) := Matrix.map_mul (f := (cA σ).toRingHom)

theorem at_realAd_mul (t : ℝ) (s : AF F) : At (evI F) (realAd F t * s) := fun c hc => by
  have h1 : c.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hc
  show c * (realAd F t * s) = 0
  refine Prod.ext ?_ ?_
  · show c.1 * (realAd F t * s).1 = 0
    rw [h1, zero_mul]
  · show c.2 * ((realAd F t).2 * s.2) = 0
    have : (realAd F t).2 = 0 := rfl
    rw [this, zero_mul, mul_zero]

theorem tr_realAd_mul (t : ℝ) (s : AF F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (realAd F t * s)) =
      t * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F s) := by
  rw [Dense.evI_mul, Dense.evI_realAd, ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem td_realAd_zero : realAd F 0 = 0 := by simp only [realAd, map_zero]

theorem evI_neg' (a : AF F) : evI F (-a) = -evI F a := map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1

theorem td_map_incM {w : InfinitePlace F} (τ : EmbOver E w) {p q : Type} (N : Matrix p q E) :
    (incM F N).map (piInf τ) = N.map τ.1 := by
  ext i j
  exact (GlobalTheory.CompanionTheory.CMAdele.piInf_tmul τ 1 (N i j)).trans (by rw [show (1 : AF F).1 w = 1 from rfl, map_one, one_mul]; rfl)

end PositivityTheory.SiegelWeilFormula.KK
