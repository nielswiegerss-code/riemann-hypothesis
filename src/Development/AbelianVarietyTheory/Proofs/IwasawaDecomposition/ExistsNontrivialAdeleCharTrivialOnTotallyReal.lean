module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharOfTrace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import GroundTheory.GlobalFields.TateThesis.AdelicChar

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.CharZero

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
theorem _root_.GlobalTheory.GaugeEx.CharZero.exists_isCharAF :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ ψ, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF F ψ := by
  intro F _ _ _
  let L : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F →+ ℂ :=
    Complex.ofRealHom.toAddMonoidHom.comp (GroundTheory.Global.infiniteTrace F)
  have hL : Continuous L := by
    change Continuous fun x => (GroundTheory.Global.infiniteTrace F x : ℂ)
    exact Complex.continuous_ofReal.comp (GroundTheory.Global.continuous_infiniteTrace F)
  obtain ⟨ψ, hψ, -⟩ :=
    _root_.GlobalTheory.StdAdelicChar.exists_char_of_trace F L hL fun x => by
      change (GroundTheory.Global.infiniteTrace F (algebraMap F (InfiniteAdeleRing F) x) : ℂ) = _
      rw [GroundTheory.Global.infiniteTrace_algebraMap F x, Complex.ofReal_ratCast]
  exact ⟨ψ, hψ⟩

end GlobalTheory.GaugeEx.CharZero
