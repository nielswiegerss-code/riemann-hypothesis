module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.FrameSignEqHermitianSign
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Avac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem not_herm_skew {B : Base F E} {m r s : ℕ} (hm : 1 ≤ m) {A : Spc F E m} (h1 : A.IsHerm σ B r s)
    (h2 : A.IsSkew σ B r s) : False := by
  have h0 : A.J = 0 := by
    ext i j
    have a := h1.herm i j
    have b := h2.skew i j
    rw [a] at b
    have : (2 : E) * A.J i j = 0 := by linear_combination b
    simpa using this
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨hrs, M, hM⟩ := h1.sig w
  rw [h0, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul] at hM
  rcases Nat.eq_zero_or_pos r with hr | hr
  · have hs : 0 < s := by omega
    have := congrFun (congrFun hM (Sum.inr ⟨0, hs⟩)) (Sum.inr ⟨0, hs⟩)
    simp at this
  · have := congrFun (congrFun hM (Sum.inl ⟨0, hr⟩)) (Sum.inl ⟨0, hr⟩)
    simp at this

end PositivityTheory.SiegelWeilFormula.Avac
