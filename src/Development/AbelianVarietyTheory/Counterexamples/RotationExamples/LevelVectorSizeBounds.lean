module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LiftFormsMainTerm
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
namespace GlobalTheory.Survey.LevelVectorSizeBounds
variable {D : D7}

theorem hookProd_pos (μ : YoungDiagram) : 0 < Formalism.LatticeIndexTer.hookProd μ := by
  unfold Formalism.LatticeIndexTer.hookProd
  refine Finset.prod_pos fun x hx => ?_
  have hx' : (x.1, x.2) ∈ μ := hx
  have a := YoungDiagram.mem_iff_lt_rowLen.1 hx'
  have b := YoungDiagram.mem_iff_lt_colLen.1 hx'
  omega

theorem locK_eq_one {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {P : HeightOneSpectrum (𝓞 E)}
    (h : χ.UnrAt P) (a : 𝓞 E) (k : Eˣ) (hk : (k : E) = a) (ha : a ∉ P.asIdeal) : χ.locK P k = 1 := by
  refine h _ ?_
  show Valued.v (((k : E)) : P.adicCompletion E) = 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hk]
  have := (P.valuation_eq_one_iff_notMem (K := E) (r := a)).2 ha
  exact this

theorem not_both {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : q ≠ p) (h1 : (p : 𝓞 E) ∈ P.asIdeal) (h2 : (q : 𝓞 E) ∈ P.asIdeal) : False := by
  have hc : IsCoprime (q : 𝓞 E) (p : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hq hp).2 hne)
  obtain ⟨x, y, hxy⟩ := hc
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hxy ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ h2) (P.asIdeal.mul_mem_left _ h1)))

theorem q_mem {P : Pl D.host.E} {q : ℕ} (h : Nat.card (kP P) = q) : (q : 𝓞 D.host.E) ∈ P.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← h]
  have := card_nsmul_eq_zero' (G := kP P) (x := 1)
  rwa [nsmul_one] at this

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)


theorem isLocal_triv : IsLocalLevel (D := D) R.triv := by
  refine ⟨fun _ => ⊥, fun _ => 1, ?_⟩
  have key : ∀ (H : Subgroup (G0 R.Pg D.R.r)) (c : H →* ℂˣ), H = ⊥ → R.triv = ⟨H, c⟩ := by
    rintro H c rfl
    have : c = 1 := by ext x; rw [Subsingleton.elim x 1]; simp
    subst this; rfl
  exact key _ _ (Subgroup.pi_bot)

theorem grp_triv (i : Fin D.R.m) (t : T) (m) :
    grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) R.triv m) = (levEnv _ (R.βV i) (R.datVt i t)).J := rfl

theorem eq_one_of_full_upper_block_eq_one {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (e : n = r) (g : GL (Fin n) κ) (h : upperLeftBlock hr g = 1) : g = 1 := by
  subst e
  have hg : g ∈ blockTri (κ := κ) (n := n) (blk2 n) := by
    intro a b hab
    simp [blk2] at hab
  unfold upperLeftBlock at h
  rw [extendOne_of_mem _ hg] at h
  have h2 := congrArg (fun x : GL (Fin n) κ => (x : Matrix (Fin n) (Fin n) κ)) h
  ext a b
  exact congrFun (congrFun h2 a) b

theorem omegaG_triv (i : Fin D.R.m) (m) (y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) :
    Datum.omegaG (R.datWp i R.triv) m y = Datum.omegaK R.Pg y := by
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have key : ∀ g : ∀ PP : ↥R.Pg, GL (Fin (Wc D i).rank) (kP PP.1),
      (fun PP => upperLeftBlock (r_le_rank_Wc i) (g PP)) ∈ (⊥ : Subgroup (G0 R.Pg D.R.r)) → ∀ PP, g PP = 1 := fun g hg PP =>
    eq_one_of_full_upper_block_eq_one _ hrk _ (congrFun (Subgroup.mem_bot.1 hg) PP)
  unfold Datum.omegaG Datum.omegaK
  split_ifs with h1 h2 h2
  · have hg := key _ h1.2.choose_spec.2.2
    have e1 : (R.datWp i R.triv).s = 0 := rfl
    have e2 : ∀ x, (R.datWp i R.triv).P.chi x = 1 := fun _ => rfl
    rw [e2]
    simp only [e1, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, Units.val_one, one_mul]
    refine Finset.prod_eq_one fun PP _ => ?_
    rw [hg PP]; simp
  · exfalso
    refine h2 fun PP hP => ⟨h1.1 PP hP, ?_⟩
    obtain ⟨g, g1, -, g3⟩ := h1.2
    exact (g1 ⟨PP, hP⟩).symm.trans (congrArg Units.val (key g g3 ⟨PP, hP⟩))
  · exfalso
    refine h1 ⟨fun PP hP => (h2 PP hP).1, fun _ => 1, fun PP => (h2 PP.1 PP.2).2.symm, fun _ => Subgroup.one_mem _, ?_⟩
    have : (fun PP : ↥R.Pg => upperLeftBlock (r_le_rank_Wc i) (1 : GL (Fin (Wc D i).rank) (kP PP.1))) = 1 := by
      funext PP; exact blockDiagonalExtendByOnePrimeField_one _ _
    exact this ▸ Subgroup.one_mem _
  · rfl


theorem levFn_congr {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (r : ℕ) (hr : r ≤ n) (t s : ℕ) (Pg Q : Finset (Pl D.host.E))
    (P : LevelP Pg r ℂ) (cg cg' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (xq xq' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (h1 : ∀ c, ∀ PP ∈ Pg, cg c PP = cg' c PP) (h2 : ∀ PP ∈ Q, xq PP = xq' PP) (x) :
    levFn β ⟨r, hr, t, s, Pg, Q, P, cg, xq⟩ x = levFn β ⟨r, hr, t, s, Pg, Q, P, cg', xq'⟩ x := by
  unfold levFn
  congr 1
  · congr 1
    exact Finset.prod_congr rfl fun PP hP => Finset.prod_congr rfl fun c _ => by dsimp only; rw [h1 _ PP hP]
  · exact Finset.prod_congr rfl fun PP hP => by dsimp only; rw [h2 PP hP]


include R in
theorem delta_base (i : Fin D.R.m) : deltaAtEmb D i (sg0 D A) = RealDat.Delta i := by
  have hl : ∀ ρ, lab (sg0 D A) ρ = ρ := fun ρ => by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0]; exact GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm.lab_base ρ
  unfold deltaAtEmb RealDat.Delta
  congr 1 <;> funext ρ
  · unfold aPlAt; rw [hl]
  · unfold aMiAt; rw [hl]

end GlobalTheory.Survey.LevelVectorSizeBounds
