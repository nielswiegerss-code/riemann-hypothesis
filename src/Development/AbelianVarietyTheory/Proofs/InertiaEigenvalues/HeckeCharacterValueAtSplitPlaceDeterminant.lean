module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Formalism.LocalToGlobal.IndefiniteReal.BridgeTie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinPartMulIncAMem
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult



namespace GlobalTheory.HeckeDetValue

theorem chr_detAt : ∀ {D : D7} (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (Q : Finset (Pl D.host.E)) (V : HSp D) (P : Pl D.host.E) (k : ℕ) (α : GA D V) (z : (AE D)ˣ), ChrEq c χ → GlobalTheory.ExportSeries.UnramOutside c Q → GlobalTheory.ExportSeries.SplitSet Q → Bridge.SplitOff P (Q : Set (Pl D.host.E)) → IsHeckeAt V P k α → IsDetAt (idemAt P) V α z → ((c z : Circle) : ℂ) = ((χ.val P : ℂˣ) : ℂ) ^ k := by
  intro D c χ Q V P k α z hc hU hS hoff hα hz
  exact GlobalTheory.HeckeDetChar.chi_detAt hc hU hS hoff hα hz

end GlobalTheory.HeckeDetValue
