module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
open GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts

namespace GlobalTheory.ProjModel

theorem isArithVar_pspace (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k]
    (hd : ringKrullDim k = 1) (N : ℕ) : IsArithVar (PSpace.str k N) N := by
  have := isIntegral_of_isDomain k N
  have : IsNoetherianRing k := IsNoetherianRing.of_finite ℤ k
  have : Smooth (PSpace.str k N) := SmoothOfRelativeDimension.smooth N _
  have hc : ∀ i, topologicalKrullDim (chart k N i : Set (PSpace k N)) = (N + 1 : ℕ) := fun i => by
    rw [topologicalKrullDim_eq_of_isEmbedding (chartι k N i).isOpenEmbedding.isEmbedding
      (congrArg SetLike.coe (opensRange_chartι k N i))]
    refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim
      (R := MvPolynomial {j // j ≠ i} k)).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, hd]
    simp [add_comm]
  refine ⟨inferInstance, inferInstance, ‹_›, ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩, ?_,
    le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_)
      ((hc 0).ge.trans (topologicalKrullDim_subspace_le _ _))⟩
  · have h := (ArithBase.isArithVar_id hd).flat
    rw [Category.id_comp] at h
    infer_instance
  · obtain ⟨i, hi⟩ := exists_mem_chart k N x
    exact ⟨_, (chart k N i).isOpen, hi, (hc i).le⟩

theorem nefFib_of_isAmpleLB {k : Type} [CommRing k] [Module.Finite ℤ k] {X : Scheme.{0}} {p : X ⟶ Sp k} [IsProper p]
    (L : HermLB p) (hL : IsAmpleLB L.B) : ArInt.NefFib L := by
  intro Z i _ _ κ _ _ _ hd
  have hA := hL.pull_of_isClosedImmersion i
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  have : IsProper (strHom κ (X := Z)) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  have h := (isNef_iff_isClosedImmersion.1 (hA.isNef (k := κ))).2 Z (𝟙 Z) inferInstance inferInstance hd
    (by rw [Category.id_comp]; infer_instance)
  rw [interNumOn_id] at h
  refine h.trans_eq (congrArg _ (funext fun j => ?_))
  fin_cases j
  rfl

variable (F : Type) [Field F] [NumberField F] (n : ℕ)

end GlobalTheory.ProjModel
