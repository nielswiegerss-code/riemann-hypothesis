module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws

@[expose] public section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels

theorem charpoly_redF (D : D7) (i : D.nd.Loc) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i))
    (s : G D.host.E D.nd.Om) :
    Matrix.charpoly ((redF D i ρ s : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
      ((ρ s : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly.map
        ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) := by
  rw [← Matrix.charpoly_map]
  rfl

end GlobalTheory.TypeLeaf
