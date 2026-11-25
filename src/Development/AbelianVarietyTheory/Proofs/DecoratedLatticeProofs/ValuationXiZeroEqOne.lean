module

import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualOrthAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodIdealZpowCompletionAdeleConjIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFrameProperties
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmulOfMemFlagSubOne
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotLineLatAtZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.SeeSaw.CoreGlue

open GlobalTheory.FinPl.FrameLat GlobalTheory.SeeSaw.LiftModel

variable {D : D7}

theorem rat_mulVec_mem {S T : HSp D} (m : Matrix (Fin T.rank) (Fin S.rank) D.host.E) {L : Lat S} {L' : Lat T}
    (h : ∀ x ∈ L, m *ᵥ x ∈ L') {P : Pl D → Prop} {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    (rat m : Mx D T.rank S.rank) *ᵥ y ∈ latV T L' P := by
  first | exact _root_.GlobalTheory.OrthSumLat.rat_mulVec_mem_latV | exact @_root_.GlobalTheory.OrthSumLat.rat_mulVec_mem_latV | apply _root_.GlobalTheory.OrthSumLat.rat_mulVec_mem_latV <;> assumption

theorem dsum_eq {S : HSp D} (x y : Fin S.rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * S.gram i j * y j = star x ⬝ᵥ S.gram *ᵥ y := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem pair_iA {S A B : HSp D} (o : OrthDec S A B) (a : Fin A.rank → D.host.E) (y : Fin S.rank → D.host.E) :
    star (o.iA *ᵥ a) ⬝ᵥ S.gram *ᵥ y = star a ⬝ᵥ A.gram *ᵥ (o.qA *ᵥ y) := by
  exact GlobalTheory.OrthSumLat.pair_iA' o a y

theorem exists_orthSum {S A B : HSp D} (o : OrthDec S A B) {LA : Lat A} {LB : Lat B} (hA : IsSelfDualC A LA)
    (hB : IsSelfDualC B LB) : ∃ L : Lat S, IsSelfDualC S L ∧ ∀ v, OrthAt o L LA LB v := by
  exact GlobalTheory.OrthSumLat.exists_selfDual_orthAt D S A B o LA LB hA hB

theorem mem_latV_one {S : HSp D} (L : Lat S) {P : Pl D → Prop} {v : Pl D} (hv : P v) (y : Fin S.rank → AE D) :
    y ∈ latV S L (· = v) ↔ y ∈ latV S L P ∧ ∀ i, y i ∈ idAt D (· = v) := by
  refine ⟨fun h => ⟨AddSubgroup.closure_mono ?_ h, latV_supp h⟩, fun h => ?_⟩
  · rintro _ ⟨α, h1, h2, r⟩
    exact ⟨α, h1, fun w hw => h2 w fun e => hw (e ▸ hv), r⟩
  · have key : ∀ y ∈ latV S L P, (fun i => y i * (pairA D.host.F 0 (LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E))) ∈
        latV S L (· = v) := by
      intro y hy
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨α, hα, -, c, hc, x, hx, rfl⟩ := hy
        refine AddSubgroup.subset_closure ⟨α * LatMem.indP D.host.F (· = v),
          LatMem.intAf_mul' hα (LatMem.indicatorAdele_mem_integralAdeles' _ _), fun w hw => ?_, c, hc, x, hx, ?_⟩
        · rw [map_mul, LatMem.indicatorAdele_supported _ _ w hw, mul_zero]
        · funext i
          have hp : pairA D.host.F 0 α * pairA D.host.F 0 (LatMem.indP D.host.F (· = v)) =
            pairA D.host.F 0 (α * LatMem.indP D.host.F (· = v)) := Prod.ext (zero_mul _) rfl
          rw [Algebra.TensorProduct.tmul_mul_tmul, hp, mul_one]
      | zero => simp only [Pi.zero_apply, zero_mul]; exact zero_mem _
      | add a b _ _ ha hb => simp only [Pi.add_apply, add_mul]; exact add_mem ha hb
      | neg a _ ha => simp only [Pi.neg_apply, neg_mul]; exact neg_mem ha
    have := key y h.1
    simp only [LatMem.mul_indP (h.2 _)] at this
    exact this

theorem latV_eq_at {S : HSp D} {L M : Lat S} {P : Pl D → Prop} (h : latV S M P = latV S L P) {v : Pl D} (hv : P v) :
    latV S M (· = v) = latV S L (· = v) := by
  ext y
  rw [mem_latV_one M hv, mem_latV_one L hv, h]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_modify {ι : Type} {p : ι → SplitPt D k} (hp : Function.Injective fun i => (p i).v) {S : HSp D} {n : Type}
    [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n) (Λ : ι → Submodule 𝒪[k] (n → k)) (hΛ : ∀ i, (Λ i).IsFullLattice k)
    {L : Lat S} (hL : IsSelfDualC S L) (l : List ι) : ∃ M : Lat S, IsSelfDualC S M ∧ (∀ i ∈ l, (β i).IsLat M (Λ i)) ∧
      ∀ v, (∀ i, v ≠ (p i).v) → latV S M (· = v) = latV S L (· = v) := by
  induction l with
  | nil => exact ⟨L, hL, by simp, fun _ _ => rfl⟩
  | cons i l ih =>
    obtain ⟨M, hM, h1, h2⟩ := ih
    obtain ⟨M', hM', h3, h4⟩ := (_root_.GlobalTheory.FrameAt.frame_facts D k (p i) S n (β i)).2.2.2.2.1 M (Λ i) hM (by first | exact hΛ i)
    refine ⟨M', hM', fun i' hi' => ?_, fun v hv => (latV_eq_at h4 (hv i)).trans (h2 v hv)⟩
    by_cases e : i' = i
    · subst e; exact h3
    · intro x
      rw [latV_eq_at h4 (fun e' => e (hp e'))]
      exact h1 i' ((List.mem_cons.1 hi').resolve_left e) x

theorem eq_sec_add (p : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = p.v)) :
    a = p.sec (p.pr a) + cA D (p.sec (p.pr (cA D a))) := by
  rw [p.sec_pr, p.sec_pr, RingHom.map_mul, cA_cA, ← add_mul, (idem_iff p a).1 ha]

theorem mem_intAt_iff (p : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = p.v)) :
    a ∈ intAt D (· = p.v) ↔ p.pr a ∈ 𝒪[k] ∧ p.pr (cA D a) ∈ 𝒪[k] := by
  refine ⟨fun h => ⟨_root_.GlobalTheory.SplitCharCond.pr_int p h.2, _root_.GlobalTheory.SplitCharCond.pr_int p ((cA_int_iff a).2 h.2)⟩, fun h => ⟨ha, ?_⟩⟩
  rw [eq_sec_add p ha, RingHom.map_add (f := _)]
  exact add_mem ((p.int_iff _).1 h.1) ((cA_int_iff _).2 ((p.int_iff _).1 h.2))

theorem single_mem_glued_iff {n : Type} [DecidableEq n] (q : Unif k) (P : Pair k n) (t : k) :
    (Pi.single (Sum.inr 0) t : n ⊕ Fin 1 → k) ∈ gluedS q 1 P.ker P.vec ↔ t ∈ 𝒪[k] := by
  have h0 : (Pi.single (Sum.inr 0) t : n ⊕ Fin 1 → k) ∘ Sum.inl = 0 := by
    funext j
    simp
  rw [GlobalTheory.LevelUnfold.mem_gluedS, h0]
  constructor
  · rintro ⟨s, h1, h2⟩
    have h3 := (h2 0).1 rfl
    rw [Pi.single_eq_same] at h3
    rw [zero_sub, neg_mem_iff, Pair.mem_ker] at h1
    have h4 := (P.hasVal_vec.smul s).unique h1
    rw [mul_one, IsLocalRing.residue_eq_zero_iff, q.mem_max_iff] at h4
    obtain ⟨c, rfl⟩ := h4
    rw [h3, Unif.inv, Subring.coe_mul, ← mul_assoc, inv_mul_cancel₀ q.ne_zero, one_mul]
    exact c.2
  · intro ht
    refine ⟨q.1 * ⟨t, ht⟩, ?_, fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩
    · rw [zero_sub]
      exact neg_mem (Pair.smul_mem_ker (Ideal.mul_mem_right _ _ q.mem_max) P.hasVal_vec.mem)
    · obtain rfl : i = 0 := Subsingleton.elim _ _
      rw [Pi.single_eq_same, Unif.inv, Subring.coe_mul, ← mul_assoc, inv_mul_cancel₀ q.ne_zero, one_mul]

theorem pair_sumFrame {p : SplitPt D k} {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) {n : Type} [Fintype n]
    [DecidableEq n] {β : Frame p A n} {β₀ : Frame p S (n ⊕ Fin 1)} (hs : IsSumFrame o ζ β β₀) (x : n ⊕ Fin 1 → k) (t : k) :
    ∑ i, ∑ j, (β₀.b *ᵥ x) i * p.pr (cA D (incA D (S.gram i j))) * (t * p.pr (incA D (star (vecB o ζ j)))) =
      t * (p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)) * x (Sum.inr 0)) := by
  let f : D.host.E →+* k := p.pr.comp (incA D)
  let r : Fin S.rank → D.host.E := star (vecB o ζ) ᵥ* S.gram
  have hr : ∀ i, r i = ∑ j, star (S.gram i j) * star (vecB o ζ j) := fun i => by
    simp only [r, vecMul, dotProduct, Pi.star_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm, ← conjTranspose_apply, gram_conjTranspose]
  have h1 : ∑ i, ∑ j, (β₀.b *ᵥ x) i * p.pr (cA D (incA D (S.gram i j))) * (t * p.pr (incA D (star (vecB o ζ j)))) =
      t * ((f ∘ r) ⬝ᵥ β₀.b *ᵥ x) := by

    simp only [dotProduct, Function.comp_apply, hr, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    change _ * f (star (S.gram i j)) * (t * f (star (vecB o ζ j))) = _
    ring
  have hA : r ᵥ* o.iA = 0 := by
    simp only [r, vecB, star_mulVec, vecMul_vecMul, o.orth, vecMul_zero]
  have hB : r ⬝ᵥ vecB o ζ = star ζ ⬝ᵥ L.gram *ᵥ ζ := by
    rw [← o.isoB]
    simp only [r, vecB, star_mulVec, vecMul_vecMul, dotProduct_mulVec]
  have hA' : (f ∘ r) ᵥ* o.jA.map p.pr = 0 := by
    funext i
    have := RingHom.map_vecMul f o.iA r i
    rw [hA, Pi.zero_apply, map_zero] at this
    exact this.symm
  have hB' : (f ∘ r) ⬝ᵥ (fun i => p.pr (ratV (vecB o ζ) i)) = p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)) := by
    rw [← hB]
    exact (RingHom.map_dotProduct f r (vecB o ζ)).symm
  rw [h1, hs, dotProduct_mulVec, vecMul_fromCols, ← vecMul_vecMul, hA', zero_vecMul, ← hB']
  congr 1
  simp [dotProduct, vecMul, Fintype.sum_sum_type]

theorem line_of_glued {p : SplitPt D k} {ρ : ℕ} {B : BesLev D ρ} {M : Lat B.V₀} {q : Unif k} {n : Type} [Fintype n] [DecidableEq n]
    {β : Frame p B.A n} {β₀ : Frame p B.V₀ (n ⊕ Fin 1)} {P : Pair k n} (hM : IsSelfDualC B.V₀ M) (hg : GluedCore B M q β β₀ P)
    {a : AE D} (ha : a ∈ idAt D (· = p.v)) :
    a • ratV (vecB B.o B.ζ) ∈ latV B.V₀ M (· = p.v) ↔ a ∈ intAt D (· = p.v) := by
  have hdec : a • ratV (vecB B.o B.ζ) = (fun i => p.sec ((β₀.b *ᵥ (Pi.single (Sum.inr 0) (p.pr a) : n ⊕ Fin 1 → k)) i)) +
      fun i => cA D (p.sec (p.pr (cA D a) * p.pr (incA D (star (vecB B.o B.ζ i))))) := by
    funext i
    have e := eq_sec_add p (Ideal.mul_mem_right (incA D (vecB B.o B.ζ i)) _ ha)
    rw [RingHom.map_mul, RingHom.map_mul (cA D), RingHom.map_mul, cA_incA] at e
    refine e.trans ?_
    rw [Pi.add_apply, mulVec_single, hg.sum]
    congr 2
    exact mul_comm _ _
  have hq : valuation k ((q.1 : 𝒪[k]) : k) ≠ 0 := by simpa using q.ne_zero
  have hu : valuation k (p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)) * q.inv) = 1 := by
    rw [map_mul, hg.norm, Unif.inv, map_inv₀, mul_inv_cancel₀ hq]
  rw [hdec, decomp hM, ← hg.lat, single_mem_glued_iff, mem_intAt_iff p ha, csec_mem_iff hM]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h x hx => ?_⟩
  · have h1 := h _ ((hg.lat _).1 (GlobalTheory.LevelUnfold.mem_gluedS.2 ⟨1, (by simp : Sum.elim P.vec (fun _ => q.inv) ∘ Sum.inl - (1 : 𝒪[k]) • P.vec ∈ P.ker),
      fun i => ⟨fun _ => by simp, fun hi => absurd hi (by omega)⟩⟩))
    rw [pair_sumFrame B.o B.ζ hg.sum, Sum.elim_inr, Valuation.mem_integer_iff, map_mul, hu, mul_one] at h1
    exact h1
  · have hx' : x = β₀.b *ᵥ (β₀.b' *ᵥ x) := by rw [mulVec_mulVec, β₀.bb', one_mulVec]
    rw [hx'] at hx
    obtain ⟨s, -, hs⟩ := GlobalTheory.LevelUnfold.mem_gluedS.1 ((hg.lat _).2 hx)
    rw [hx', pair_sumFrame B.o B.ζ hg.sum, (hs 0).1 rfl, ← mul_assoc _ q.inv]
    exact mul_mem h (mul_mem ((Valuation.mem_integer_iff _ _).2 hu.le) s.2)

end GlobalTheory.SeeSaw.CoreGlue
