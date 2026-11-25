module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk ValuativeRel

namespace GlobalTheory.SeeSaw.Resc

variable {D : D7}

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (s : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (s • f) = s • heisO ψ S T w f := by
  funext x; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

end GlobalTheory.SeeSaw.Resc

namespace GlobalTheory.SeeSaw.Resc

variable {D : D7} {m n : ℕ}

theorem dRho_smul (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ))
    (hh : ∀ w (s : ℂ) f, hs w (s • f) = s • hs w f) (θ : InfFam D) (τ : D.what₂.Tau)
    (z : Matrix (Fin m) (Fin n) ℂ) (s : ℂ) (f : Mx D m n → ℂ) :
    Datum.dRho hs θ τ z (s • f) = s • Datum.dRho hs θ τ z f := by
  funext x
  simp only [Datum.dRho, hh, Pi.smul_apply, smul_eq_mul]
  exact deriv_const_mul_field _

theorem aPlusAll_smul (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ))
    (hh : ∀ w (s : ℂ) f, hs w (s • f) = s • hs w f) (θ : InfFam D)
    (J : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ → Matrix (Fin m) (Fin n) ℂ)
    (B : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (k) (s : ℂ) (f : Mx D m n → ℂ) :
    aPlusAll hs θ J B B' k (s • f) = s • aPlusAll hs θ J B B' k f := by
  simp only [aPlusAll, aPlus, crea, dRho_smul hs hh, smul_sub, smul_comm s]

theorem opPow_smul {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (hA : ∀ i (s : ℂ) f, A i (s • f) = s • A i f)
    (k : ι →₀ ℕ) (s : ℂ) (f : X → ℂ) : opPow A k (s • f) = s • opPow A k f := by
  unfold opPow
  induction (Multiset.toList (Finsupp.toMultiset k)) with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, ih, hA]

theorem pureTensorL_smul {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (hA : ∀ i (s : ℂ) f, A i (s • f) = s • A i f)
    (s : ℂ) (f : X → ℂ) : pureTensorL A (s • f) = s • pureTensorL A f := by
  unfold pureTensorL
  have : (fun k : ι →₀ ℕ => opPow A k (s • f)) = s • fun k => opPow A k f := by
    funext k; exact opPow_smul A hA k s f
  rw [this, map_smul]

end GlobalTheory.SeeSaw.Resc

namespace GlobalTheory.SeeSaw.Resc

variable {D : D7}

theorem pureTensorO_smul (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (s : ℂ) (f : WO S T → ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (s • f) = s • pureTensorO ψ θ S T sS sT BS BT f :=
  pureTensorL_smul _ (aPlusAll_smul _ (heisO_smul ψ S T) _ _ _ _) s f

end GlobalTheory.SeeSaw.Resc
