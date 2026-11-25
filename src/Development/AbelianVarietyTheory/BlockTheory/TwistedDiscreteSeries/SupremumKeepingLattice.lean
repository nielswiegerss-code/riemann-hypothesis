module

public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints

@[expose] public section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticePartsOverBalls

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Arith Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (i : Fin D.R.m)

variable {T R κ v₀ i}

theorem base_of_tie (fw : FWTie T R κ v₀) : res T (sg0 D A) = T.σ₀ ∧ GoodEmb T.Q.c (res T (sg0 D A)) ∧
    T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := by
  have hg := Formalism.IndefR.FWT.base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1
  refine ⟨?_, hg, fw.laws.spaceW _ (inR i) _ hg⟩
  rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0]
  exact res_embLL T fw.alg_eq fw.laws.pins.2.2.1

end GlobalTheory.IndefiniteRowSideFullHecke.LatticePartsOverBalls
