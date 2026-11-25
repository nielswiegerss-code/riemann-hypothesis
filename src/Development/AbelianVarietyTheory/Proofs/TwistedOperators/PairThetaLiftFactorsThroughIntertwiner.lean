module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivariantMapCarriesGelfandInvariantToFunction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonzeroFockVacuumOfNonzeroThetaFunction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorsOfThetaDatumInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegrationByPartsRightDerivativeAdelicQuotient
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsIrrOfEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoverKerOfDown
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesPureInnerProductsTensorProduct
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfContr
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEmbeddingSkew
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialIsoUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsKActOfStable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryImage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupportOfAdmissible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InclTprodUpdate
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnMulRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspGrowOfMemSpan
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ItEqSumKMean
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KMeanMemKFinOfCoefFam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocKerOfCoverKer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoIntertwinerSmallerFockToDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignBlockDeterminantNeZeroOfMemMaxCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubstitutionTotalDegreeLe
import Development.AbelianVarietyTheory.Statements.HaarFundamentalDomain.ExistsHaarFundDom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid GlobalTheory.Chain.RealIt GlobalTheory.Chain.IoLift
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.PairLift
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.PointAtPlaceHom

namespace GlobalTheory.PairLift.RuleLift

variable {D : D7}

variable {V W : HSp D} {S S' : D.what₂.Tau → SPar}

theorem exists_local {X : ProvA} (hX : ChosenSeries X) (h5 : GlobalTheory.Published.HarishChandraModules)
    (hB : ModelsAreCoverSeries D) (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) {aS aT : ℚ}
    (hR : RulePar X (S τ) (S' τ) aS aT) :
    (kFin M τ ≤ M.sm τ ∧ kFin M' τ ≤ M'.sm τ) ∧ ∃ a a', IsKAct M τ a ∧ IsKAct M' τ a' ∧
      AbsIrr (fun X : lieAt V τ => a X) ∧ LocKer M M' τ aS aT a' := by
  obtain ⟨p, q, r, s, l₁, l₂, l₁', l₂', h1, h2, h1', h2', hR, hS, hS'⟩ := hR
  obtain ⟨⟨e, he⟩, m, hm, hU⟩ := hB.1 X V S M τ p q l₁ l₂ aT ⟨hR.pos, h1, h2, hR.par, hX _ _ _ hR.par, hS⟩
  obtain ⟨⟨e', he'⟩, m', hm', hU'⟩ := hB.2 X W S' M' τ r s l₁' l₂' aS ⟨hR.pos', h1', h2', hR.par', hX _ _ _ hR.par', hS'⟩
  obtain ⟨U, hU⟩ := hU e he
  obtain ⟨U', hU'⟩ := hU' e' he'
  obtain ⟨κ, hκ⟩ := PolyIso.exists_isPolyIso _ _ _ _ _ _ _ _ e e' he he'
  obtain ⟨s₁, a, ha⟩ := GlobalTheory.Chain.IoLift.kFin_smooth_isKAct D V S M τ _ _ _ _ _ _ _ hU
  obtain ⟨s₂, a', ha'⟩ := GlobalTheory.Chain.IoLift.kFin_smooth_isKAct D W S' M' τ _ _ _ _ _ _ _ hU'
  have i1 := GlobalTheory.SmallerSource.discrete_series_gk_admissible_irreducible X (h5.admQ5_of_harishChandraModules X) hR.pos (ofBlocks l₁ l₂ : Ix p q → ℚ)
  have i2 := GlobalTheory.SmallerSource.discrete_series_gk_admissible_irreducible X (h5.admQ5_of_harishChandraModules X) hR.pos' (ofBlocks l₁' l₂' : Ix r s → ℚ)
  refine ⟨⟨s₁, s₂⟩, a, a', ha, ha', GlobalTheory.KFinIrr.absIrr_kFin D V S M τ _ _ _ _ _ m U.toLinearEquiv a hU i1.2 i1.1 ha, ?_⟩
  exact GlobalTheory.Chain.IoLift.KerTransfer.locKer_of_coverKer D V W S S' M M' τ _ _ _ _ _ _ _ _ e e' m m' aS aT U U' κ a' hm' hU hU' hκ ha'
    (GlobalTheory.Chain.IoLift.CoverKernel.coverKer_of_down X _ _ _ _ _ _ hR.down i1.2 (GlobalTheory.Chain.IoLift.UImg.unitaryImage _ _ _ _)
      (GlobalTheory.Chain.IoLift.finiteSupport_of_admissible _ _ _ _ _ _ i2.1) GlobalTheory.Chain.IoLift.TensorFormProof.tensorForm)

theorem signBlockDeterminant_zpow_eq_of_agree {n : ℕ} (ε : Fin n → Bool) (w : Bool → ℚ) {x x₀ : Bool → ℤ} (hx : ∀ j, (x (ε j) : ℚ) = w (ε j))
    (hx₀ : ∀ j, (x₀ (ε j) : ℚ) = w (ε j)) (e : Bool) (g : Matrix (Fin n) (Fin n) ℂ) :
    signBlockDeterminant ε e g ^ x e = signBlockDeterminant ε e g ^ x₀ e := by
  by_cases hj : ∃ j, ε j = e
  · obtain ⟨j, rfl⟩ := hj
    have : x (ε j) = x₀ (ε j) := by exact_mod_cast (hx j).trans (hx₀ j).symm
    rw [this]
  · simp only [not_exists] at hj
    have : IsEmpty {a // ε a = e} := ⟨fun a => hj a.1 a.2⟩
    rw [signBlockDeterminant, Matrix.det_isEmpty, _root_.one_zpow, _root_.one_zpow]

theorem compact_transfer {V W : HSp D} {S S' : D.what₂.Tau → SPar} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {M : DSModel V S} {M' : DSModel W S'} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f f₀ : WO V W → ℂ}
    {τ : D.what₂.Tau} {aS aT : ℚ} (hinj : Function.Injective (ptOf ψ θ M M' f₀))
    (hc : CompactFock ψ θ M M' ω f τ aS aT) (hc₀ : CompactFock ψ θ M M' ω f₀ τ aS aT)
    {h : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hh : h ∈ Formalism.REAL.Kset (M.ε τ))
    {k : Matrix (Fin W.rank) (Fin W.rank) ℂ} (hk : k ∈ Formalism.REAL.Kset (M'.ε τ)) {φ φ' : PolF D W.rank V.rank}
    (e : ω (elt θ M τ h, elt θ M' τ k) (ptOf ψ θ M M' f₀ φ) = ptOf ψ θ M M' f₀ φ') :
    ω (elt θ M τ h, elt θ M' τ k) (ptOf ψ θ M M' f φ) = ptOf ψ θ M M' f φ' := by
  obtain ⟨x, y, hx, hy, hc⟩ := hc
  obtain ⟨x₀, y₀, hx₀, hy₀, hc₀⟩ := hc₀
  let pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ) := pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f
  let pt₀ : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ) := pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f₀
  have hp : ptOf ψ θ M M' f = pt := rfl
  have hp₀ : ptOf ψ θ M M' f₀ = pt₀ := rfl
  have e1 := hc₀ h hh k hk φ
  rw [e, hp₀, ← map_smul] at e1
  have e2 := hinj (show ptOf ψ θ M M' f₀ φ' = ptOf ψ θ M M' f₀ _ from e1)
  rw [hc h hh k hk φ, e2, hp, map_smul, signBlockDeterminant_zpow_eq_of_agree (M.ε τ) _ hx hx₀, signBlockDeterminant_zpow_eq_of_agree (M.ε τ) _ hx hx₀,
    signBlockDeterminant_zpow_eq_of_agree (M'.ε τ) _ hy hy₀, signBlockDeterminant_zpow_eq_of_agree (M'.ε τ) _ hy hy₀]



theorem pairLifts (D : D7) (X : ProvA) (hI : Inputs D X) (hC : CuspAll D X) : PairLifts D X := by
  intro S S' aS aT hR V W M M' θ ψ hθ ω hω f₀ It hf₀ hIt ν 𝓕 hν h𝓕 f hf F hF
  obtain ⟨χS, χT, hω', he⟩ := hω
  by_cases hf0 : f = 0
  · subst hf0
    have e : ∀ p, ptOf ψ θ M M' 0 p = 0 := fun p => GlobalTheory.Mem.VacReal.ptF_zero ψ θ (Fr.ofModel M) (Fr.ofModel M') p
    refine ⟨0, zero_mem _, fun p v g => ?_⟩
    simp only [e, thetaKO, map_zero, Pi.zero_apply, zero_mul, integral_zero, LinearMap.zero_apply]
    exact ⟨integrableOn_zero, trivial⟩
  have hvf : IsVacVec ψ θ M M' f := ⟨hf.1, hf0, hf.2⟩
  have key := fun τ => exists_local hI.chosen hI.hc hI.bridge M M' τ (hR τ)
  choose hs a a' ha ha' hirr hker using key
  have h : KSm M := fun τ => (hs τ).1
  have h' : KSm M' := fun τ => (hs τ).2
  have hv := fun τ => hI.vacChar V W _ _ M M' θ ψ χS χT ω f τ _ _ hθ hω' (he τ).1 (he τ).2 hvf
  have hv₀ := fun τ => hI.vacChar V W _ _ M M' θ ψ χS χT ω f₀ τ _ _ hθ hω' (he τ).1 (he τ).2 hf₀
  have hpt : ∀ P, IsThetaFunO ψ V W (ptOf ψ θ M M' f P) := fun P =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hω'.std hθ _ _ _ _ hf.1 P
  have hinj₀ := GlobalTheory.FockInj.ptOf_injective D V W S S' ψ θ M M' f₀ hω'.std hθ hf₀
  have L := hI.laws V W θ ψ χS χT ω hθ hω' ν 𝓕 hν h𝓕
  have hcusp := hC S S' aS aT hR V W M M' θ ψ hθ ω ⟨χS, χT, hω', he⟩ ν 𝓕 hν h𝓕
  let pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ) := pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f
  have hp : ptOf ψ θ M M' f = pt := rfl
  let pt₀ : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ) := pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f₀
  have hp₀ : ptOf ψ θ M M' f₀ = pt₀ := rfl
  have hS : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) (pt φ) z)
      (pt (srcOp M M' τ (aT τ) X φ) z) 0 := fun τ X hX φ z => by
    have := (hv τ).2.2.1 X hX φ z
    simpa [hp, srcOp, sub_eq_add_neg] using this
  have hT : ∀ τ, ∀ X ∈ lieAt W τ, ∀ φ z, HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ X t) (pt φ) z)
      (pt (tgtOp M M' τ (aS τ) X φ) z) 0 := fun τ X hX φ z => (hv τ).2.2.2 X hX φ z
  have hS₀ : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) (pt₀ φ) z)
      (pt₀ (srcOp M M' τ (aT τ) X φ) z) 0 := fun τ X hX φ z => by
    have := (hv₀ τ).2.2.1 X hX φ z
    simpa [hp₀, srcOp, sub_eq_add_neg] using this
  have hT₀ : ∀ τ, ∀ X ∈ lieAt W τ, ∀ φ z, HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ X t) (pt₀ φ) z)
      (pt₀ (tgtOp M M' τ (aS τ) X φ) z) 0 := fun τ X hX φ z => (hv₀ τ).2.2.2 X hX φ z
  let C := MultT θ M' ∅ 1
  have hM : ∀ F : C, IsMultMap θ M' ∅ 1 (PiTensorProduct.lift.symm (F : SmT M' →ₗ[ℂ] (GA D W → ℂ))) := fun F =>
    (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 F.2)
  have hint : ∀ F : C, ∀ φ v g, IntegrableOn
      (fun h => thetaKO ω g h (pt φ) * (F : SmT M' →ₗ[ℂ] (GA D W → ℂ)) v h) 𝓕 ν := fun F φ v g => by
    induction v using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      have := (L.integ _ _ (hpt φ) ⟨(hM F).aut v, (hM F).cusp v⟩ g 1).const_mul r
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      beta_reduce
      rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm, rTr, mul_one]
      rfl
    | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, mul_add]; exact hx.add hy
  obtain ⟨B, hB⟩ := exists_trilinear ν 𝓕 (fun g h => LinearMap.proj 0 ∘ₗ ω (g, h)) pt C hint
  replace hB : ∀ φ v F, B φ v F =
      GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift ω ν 𝓕 (pt φ) ((F : SmT M' →ₗ[ℂ] (GA D W → ℂ)) v) := hB
  have hshift : ∀ (κ : GA D V) s F, rTr V κ (GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift ω ν 𝓕 s F) =
      GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift ω ν 𝓕 (ω (κ, 1) s) F := fun κ s F => funext fun g => by
    unfold rTr GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift Lift.liftInt thetaKO
    congr 1; funext h
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  let Fc : C := ⟨F, hF⟩
  let BF : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] (GA D V → ℂ) := B.compr₂ (LinearMap.applyₗ Fc)
  have hBF : ∀ φ v, BF φ v = GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift ω ν 𝓕 (pt φ) (F v) := fun φ v => hB φ v Fc
  have hcl : ∀ v : M'.Vec, IsAutFunSm θ W (F (PiTensorProduct.tprod ℂ v)) ∧
      IsCuspFun W (F (PiTensorProduct.tprod ℂ v)) := fun v => ⟨(hM Fc).aut v, (hM Fc).cusp v⟩
  have hBg : ∀ φ v, IsCuspGrow θ V (BF φ v) := fun φ v => by
    refine GlobalTheory.Chain.CuspGrowSpace.isCuspGrow_of_mem_span D θ V _ ?_
    induction v using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      rw [hBF]
      exact ⟨L.aut _ _ (hpt φ) (hcl v), L.smooth _ _ (hpt φ) (hcl v), hcusp _ hF _ _ (hpt φ),
        L.growth _ _ (hpt φ) (hcl v)⟩
    | add x y hx hy => rw [map_add (f := _)]; exact add_mem hx hy
  let G : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] (SmT M × (GA D V → ℂ)) :=
    (LinearMap.prodEquiv ℂ).toLinearMap ∘ₗ It.prod BF
  have hGe : ∀ φ v, G φ v = (It φ v, BF φ v) := fun _ _ => rfl
  have hav := mem_span_of_average G h' fun τ φ v => by
    obtain ⟨n, φs, c, hc, hφ₀⟩ := GlobalTheory.Chain.IoLift.FockOrbit.fock_orbit_coefFam D V W _ _ M M' θ ψ ω f₀ τ _ _ hθ hinj₀
      (hv₀ τ).2.1 φ
    have hφ : ∀ k, ω (1, elt θ M' τ (Formalism.REAL.toMK k)) (ptOf ψ θ M M' f φ) =
        ptOf ψ θ M M' f (∑ i, c i k • φs i) := fun k => by
      have := compact_transfer hinj₀ (hv τ).2.1 (hv₀ τ).2.1 (h := 1) ⟨one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩
        k.2 (φ := φ) (by rw [GlobalTheory.Chain.IoLift.elt_one hθ]; exact hφ₀ k)
      rwa [GlobalTheory.Chain.IoLift.elt_one hθ] at this
    have hk := GlobalTheory.Chain.IoLift.kMean_mem_kFin_of_coefFam D W _ M' τ n c hc (v τ)
    refine ⟨n, φs, fun i => ⟨_, h' τ (hk i)⟩, hk, Prod.ext ?_ ?_⟩
    · rw [Prod.fst_sum]
      exact GlobalTheory.Chain.IoLift.it_eq_sum_kMean D V W _ _ M M' θ ω _ It hIt τ n c φ φs v _ hc.1 hφ₀ fun _ => rfl
    · rw [Prod.snd_sum]
      funext g
      simp only [hGe, hBF, Finset.sum_apply]
      refine GlobalTheory.Chain.IoLift.AvgLift.liftInt_eq_sum_average D V W _ M' θ ψ χS χT ω ν 𝓕 hθ hω' hν h𝓕 τ n c _ _ _ _ hc.1
        (hpt φ) (fun κ => ?_) (hcl v).1.toIsAutFun (fun i x => apply_kMean (hM Fc) τ (hc.1 i) v _ rfl x) g
        (hint Fc _ _ g) fun i => hint Fc _ _ g
      rw [hφ, hp]

      simp only [map_sum, map_smul]
  obtain ⟨u, hu, hue⟩ := GlobalTheory.Chain.IoLift.exists_mult hI.ext.1 hθ
    (fun _ hφ => (GlobalTheory.Grow.rapidDec_of_unifModGrowth hI.decay hθ hφ.1 hφ.2.1 hφ.2.2.2 hφ.2.2.1).bounded)
    h h' ha ha' hirr hker It BF
    (J := ∅) (χ := 1)
    (by
      by_contra hn
      refine hIt.ne (LinearMap.ext₂ fun φ v => ?_)
      refine (Submodule.span_le (p := LinearMap.ker (LinearMap.fst ℂ _ _))).2 ?_ (hav φ v)
      rintro _ ⟨φ, y, rfl⟩
      exact by_contra fun h => hn ⟨φ, y, h⟩)
    (fun τ φ κ hκ => by
      obtain ⟨x, y, -, -, hc⟩ := (hv₀ τ).2.1
      have this₀ := hc _ hκ 1 ⟨one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩ φ
      rw [hp₀, ← map_smul, ← hp₀] at this₀
      have this := compact_transfer hinj₀ (hv τ).2.1 (hv₀ τ).2.1 hκ ⟨one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩
        this₀
      have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
      rw [GlobalTheory.Chain.IoLift.elt_one hθ, hp₀, elt, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd,
        Matrix.nonsing_inv_mul_cancel_right _ _ hd] at this₀
      rw [GlobalTheory.Chain.IoLift.elt_one hθ, hp, elt, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd,
        Matrix.nonsing_inv_mul_cancel_right _ _ hd] at this
      exact ⟨_, (MvPolynomial.totalDegree_smul_le _ _).trans (SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ _), fun v =>
        ⟨hIt.eqK τ κ (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt_subset M τ hκ) φ _ this₀.symm v, by rw [hBF, hBF, hshift, this]⟩⟩)
    (fun τ X hX φ v => hIt.eqg τ X hX φ _ (hS₀ τ X hX φ) v)
    (fun τ Y hY φ v v' hd => hIt.invg τ Y hY φ _ v v' (hT₀ τ Y hY φ) hd) hBg
    (fun τ X hX φ v => by
      induction v using PiTensorProduct.induction_on with
      | smul_tprod r v =>
        rw [map_smul, map_smul, (GlobalTheory.Mem.AutSpace.linOnSm_Rder hX).smul, hBF, hBF,
          L.derS (pt φ) _ (hpt φ) (hcl v) τ X hX]
        congr 2
        exact funext fun z => (hS τ X hX φ z).deriv.symm
      | add x y hx hy =>
        rw [map_add (f := _), map_add (f := _), hx, hy, (GlobalTheory.Mem.AutSpace.linOnSm_Rder hX).add _ (hBg _ _).2.1 _ (hBg _ _).2.1])
    (fun τ Y hY φ v w hw => by
      have e1 := GlobalTheory.MultGelf.rder_apply (hM Fc) τ v hY (v τ) w hw
      rw [Function.update_eq_self] at e1
      have e2 : GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT θ ω τ Y (pt φ) = pt (tgtOp M M' τ (aS τ) Y φ) :=
        funext fun z => (hT τ Y hY φ z).deriv
      funext g
      have := L.derT_add (hpt φ) (hcl v) τ hY g
      rw [hp, e2, add_comm] at this
      rw [Pi.add_apply, hBF, hBF]
      exact (congrArg (fun A => _ + GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift ω ν 𝓕 (pt φ) A g) e1).symm.trans this)
    fun φ v κ hκ g => absurd hκ (Set.notMem_empty κ)
  have hall : ∀ φ v, u (It φ v) = BF φ v := fun φ v => sub_eq_zero.1 (by
    refine (Submodule.span_le (p := LinearMap.ker (u ∘ₗ LinearMap.fst ℂ _ _ - LinearMap.snd ℂ _ _))).2 ?_ (hav φ v)
    rintro _ ⟨φ, y, rfl⟩
    exact sub_eq_zero.2 (hue φ y))
  refine ⟨u, hu, fun p v g => ⟨hint Fc p v g, ?_⟩⟩
  rw [hall, hBF]
  rfl

end GlobalTheory.PairLift.RuleLift
