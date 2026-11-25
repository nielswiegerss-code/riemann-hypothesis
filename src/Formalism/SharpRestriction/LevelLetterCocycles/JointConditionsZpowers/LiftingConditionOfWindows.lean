module

public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData

@[expose] public section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

open NumberField IsDedekindDomain

theorem locC_rTwO (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) :
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x) =
      twistM (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (Formalism.MainNotions.TruncatedSeriesCountingIdentities.chi1C C)⁻¹ := by
  apply MonoidHom.ext
  intro g
  apply Matrix.ext
  intro a b
  have key : ∀ u v : D.nd.O i, C.inc ((D.nbr i w hw).toLL (u * v)) =
      C.inc ((D.nbr i w hw).toLL u) * C.inc ((D.nbr i w hw).toLL v) := by
    intro u v
    rw [map_mul, map_mul]
  exact key _ _

theorem locC_cont (D : D7) (i : D.nd.Loc) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hM : Continuous fun g => M g)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (v : Fin k → ↥C.LL.1) :
    Continuous fun g => (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C M g).mulVec v := by
  have hmat : Continuous fun g => Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C M g := by
    refine continuous_matrix fun a b => ?_
    have h1 : Continuous fun g : Br.G D.nbr i w hw => M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) a b :=
      (hM.matrix_elem a b).comp (continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw))
    have h2 : Continuous fun y : D.nd.O i => (((D.nbr i w hw).eO y : ↥(OL (D.nbr i w hw).LL)) :
        ↥(D.nbr i w hw).LL.1) := continuous_subtype_val.comp (D.nbr i w hw).eO_cont
    have h3 : Continuous fun y : ↥(D.nbr i w hw).LL.1 => C.inc y :=
      Continuous.subtype_mk continuous_subtype_val _
    exact h3.comp (h2.comp h1)
  exact hmat.matrix_mulVec continuous_const

theorem rTwO_cont (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (x : D.nd.X i) : Continuous fun g => rTwO D.nd i r x g := by
  have h1 : Continuous fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) := by
    have e : (fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i)) =
        fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext g
      rw [map_inv]
      rfl
    rw [e]
    exact (D.nd.chi_cont i 1).comp continuous_inv
  exact h1.smul (hr x)

end Formalism.MainNotions.N
