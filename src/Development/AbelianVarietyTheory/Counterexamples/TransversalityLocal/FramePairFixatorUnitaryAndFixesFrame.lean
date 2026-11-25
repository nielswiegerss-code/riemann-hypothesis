module

public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

namespace GlobalTheory.NonGenericLocalCheck

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E}

theorem exists_transv {α : Type*} (rel : α → α → Prop) (hr : Equivalence rel) (S : Set α) :
    ∃ R, IsTransv rel S R := by
  classical
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨∅, Set.empty_subset _, fun x => isEmptyElim x, fun y hy => hy.elim⟩

  obtain ⟨pick, hpk⟩ : ∃ pick : α → α, ∀ x, pick x = Classical.epsilon (fun y => y ∈ S ∧ rel y x) :=
    ⟨_, fun _ => rfl⟩
  have hpick : ∀ x ∈ S, pick x ∈ S ∧ rel (pick x) x := fun x hx => by
    rw [hpk]
    exact Classical.epsilon_spec (p := fun y => y ∈ S ∧ rel y x) ⟨x, hx, hr.refl x⟩
  have hcongr : ∀ x x', rel x x' → pick x = pick x' := by
    intro x x' h
    have hset : (fun y => y ∈ S ∧ rel y x) = (fun y => y ∈ S ∧ rel y x') := by
      funext y
      exact propext ⟨fun ⟨hy, hyx⟩ => ⟨hy, hr.trans hyx h⟩,
        fun ⟨hy, hyx⟩ => ⟨hy, hr.trans hyx (hr.symm h)⟩⟩
    rw [hpk, hpk, hset]
  refine ⟨pick '' S, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (hpick x hx).1
  · intro x hx
    exact ⟨pick x, ⟨x, hx, rfl⟩, (hpick x hx).2⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ h
    exact hcongr x x' (hr.trans (hr.symm (hpick x hx).2) (hr.trans h (hpick x' hx').2))

section General
variable {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

theorem img_mul (g g' : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) : img (g * g') Λ = img g (img g' Λ) := by
  ext x
  simp only [img, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g' y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem img_one (Λ : Submodule M.L.O V) : img (1 : V ≃ₗ[E] V) Λ = Λ := by
  ext x
  simp only [img, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem trel_equiv (P : FPair H r) : Equivalence (TRel P) := by
  constructor
  · intro t
    exact ⟨1, P.St.one_mem, (img_one _).symm⟩
  · rintro t t' ⟨s, hs, h⟩
    refine ⟨s⁻¹, P.St.inv_mem hs, ?_⟩
    rw [h, ← img_mul, inv_mul_cancel, img_one]
  · rintro t t' t'' ⟨s, hs, h⟩ ⟨s', hs', h'⟩
    exact ⟨s' * s, P.St.mul_mem hs' hs, by rw [h', h, img_mul]⟩

theorem framePairFixator_unitary_and_fixes_frame (P : FPair H r) {g : V ≃ₗ[E] V} (hg : g ∈ P.UW0) :
    IsUnitary H g ∧ ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨fun x y => rfl, fun b => ⟨rfl, rfl⟩⟩
  | mul x y _ _ hx hy =>
    have hxu : ∀ u w, H.h (x u) (x w) = H.h u w := hx.1
    have hyu : ∀ u w, H.h (y u) (y w) = H.h u w := hy.1
    refine ⟨fun u w => ?_, fun b => ⟨?_, ?_⟩⟩
    · change H.h (x (y u)) (x (y w)) = H.h u w
      rw [hxu, hyu]
    · change x (y _) = _
      rw [(hy.2 b).1, (hx.2 b).1]
    · change x (y _) = _
      rw [(hy.2 b).2, (hx.2 b).2]
  | inv x _ hx =>
    have hxu : ∀ u w, H.h (x u) (x w) = H.h u w := hx.1
    refine ⟨fun u w => ?_, fun b => ⟨?_, ?_⟩⟩
    · change H.h (x.symm u) (x.symm w) = H.h u w
      have key := hxu (x.symm u) (x.symm w)
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at key
      exact key.symm
    · change x.symm _ = _
      rw [LinearEquiv.symm_apply_eq]
      exact ((hx.2 b).1).symm
    · change x.symm _ = _
      rw [LinearEquiv.symm_apply_eq]
      exact ((hx.2 b).2).symm

theorem perp_stable {g : V ≃ₗ[E] V} (hu : IsUnitary H g) (f : Fin (r + 1) → V)
    (hf : ∀ b, g (f b) = f b) {v : V} (hv : v ∈ H.perp (H.X f)) : g v ∈ H.perp (H.X f) := by
  have hfix : H.X f ≤ LinearMap.eqLocus (g : V →ₗ[E] V) LinearMap.id := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    exact LinearMap.mem_eqLocus.mpr (hf _)
  have hv' : ∀ x ∈ H.X f, H.h v x = 0 := hv
  have hu' : ∀ x y, H.h (g x) (g y) = H.h x y := hu
  show ∀ x ∈ H.X f, H.h (g v) x = 0
  intro x hx
  have hx' : g x = x := LinearMap.mem_eqLocus.mp (hfix hx)
  rw [← hx', hu']
  exact hv' x hx

theorem rel_equiv (P : FPair H r) : Equivalence (Datum.Rel (P := P)) := by
  constructor
  · intro d
    refine ⟨1, P.UW0.one_mem, fun x y h => ?_, fun x y h => ?_, fun x' y' x y h' h => ?_⟩
    · rw [show y = x from Subtype.ext h]
    · rw [show y = x from Subtype.ext h]
    · rw [show y' = x' from Subtype.ext h', show y = x from Subtype.ext h]
  · rintro d d' ⟨g, hg, h1, h2, h3⟩
    refine ⟨g⁻¹, P.UW0.inv_mem hg, fun x y hxy => ?_, fun x y hxy => ?_,
      fun x' y' x y hx' hx => ?_⟩
    · have e : (x : V) = g y := by rw [hxy]; exact (g.apply_symm_apply (x : V)).symm
      exact (h1 y x e).symm
    · have e : (x : V) = g y := by rw [hxy]; exact (g.apply_symm_apply (x : V)).symm
      exact (h2 y x e).symm
    · have e1 : (x' : V) = g y' := by rw [hx']; exact (g.apply_symm_apply (x' : V)).symm
      have e2 : (x : V) = g y := by rw [hx]; exact (g.apply_symm_apply (x : V)).symm
      exact (h3 y' x' y x e1 e2).symm
  · rintro d d' d'' ⟨g, hg, h1, h2, h3⟩ ⟨g', hg', k1, k2, k3⟩
    have sA : ∀ u : ↥(H.perp (H.X P.A.f)), g u ∈ H.perp (H.X P.A.f) := fun u =>
      perp_stable (framePairFixator_unitary_and_fixes_frame P hg).1 P.A.f (fun b => ((framePairFixator_unitary_and_fixes_frame P hg).2 b).1) u.2
    have sB : ∀ u : ↥(H.perp (H.X P.B.f)), g u ∈ H.perp (H.X P.B.f) := fun u =>
      perp_stable (framePairFixator_unitary_and_fixes_frame P hg).1 P.B.f (fun b => ((framePairFixator_unitary_and_fixes_frame P hg).2 b).2) u.2
    refine ⟨g' * g, P.UW0.mul_mem hg' hg, fun x z hz => ?_, fun x z hz => ?_,
      fun x' z' x z hz' hz => ?_⟩
    · exact (h1 x ⟨g x, sA x⟩ rfl).trans (k1 ⟨g x, sA x⟩ z hz)
    · exact (h2 x ⟨g x, sB x⟩ rfl).trans (k2 ⟨g x, sB x⟩ z hz)
    · exact (h3 x' ⟨g x', sB x'⟩ x ⟨g x, sA x⟩ rfl rfl).trans (k3 ⟨g x', sB x'⟩ z' ⟨g x, sA x⟩ z hz' hz)

theorem reps_nonempty (P : FPair H r) : Nonempty (Reps P) := by
  choose RT hRT using fun d : Datum P =>
    exists_transv (TRel P) (trel_equiv P) {t | IsTermOver P d t}
  obtain ⟨RD, hRD⟩ := exists_transv (Datum.Rel (P := P)) (rel_equiv P) Set.univ
  exact ⟨⟨RD, RT, hRD, hRT⟩⟩

end General

section Model
variable (M) (m : ℕ)

theorem theta_some {g} (h : M.split = some g) : theta M = (g.q : F) := by
  simp only [theta, h]

end Model

end GlobalTheory.NonGenericLocalCheck
