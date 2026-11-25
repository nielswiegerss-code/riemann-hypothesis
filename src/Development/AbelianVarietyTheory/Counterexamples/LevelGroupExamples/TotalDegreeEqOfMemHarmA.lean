module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlaceLabellingInertFrobeniusNotConj
public import Formalism.LocalToGlobal.ProjectiveLattices.IsThRule

@[expose] public section

namespace GlobalTheory.ThetaRuleCheck
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField MvPolynomial

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem inPsi_conjugate_iff (τ : E →+* ℂ) : InPsi H (ComplexEmbedding.conjugate τ) ↔ ¬ InPsi H τ := by
  apply GlobalTheory.InertLabelling.inPsi_conj_iff

end GlobalTheory.ThetaRuleCheck
