module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Localization.Cardinality
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Analysis.Complex.Cardinality
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl GlobalTheory.KeyPow

namespace GlobalTheory.KeyRuleUnique


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
open Cardinal in
theorem _root_.GlobalTheory.KeyRuleUnique.nonempty_ringHom_complex (K : Type) [Field K] [CharZero K]
    [Countable K] : Nonempty (K →+* ℂ) := by
  let F := FractionRing (MvPolynomial ℝ K)
  let L := AlgebraicClosure F
  let i : K →+* L := (algebraMap F L).comp ((algebraMap (MvPolynomial ℝ K) F).comp MvPolynomial.C)
  haveI : CharZero L := (RingHom.charZero_iff i.injective).1 inferInstance
  have hK : #K ≤ 𝔠 := mk_le_aleph0.trans aleph0_le_continuum
  have hP : #(MvPolynomial ℝ K) = 𝔠 := by
    rw [MvPolynomial.cardinalMk_eq_max_lift]
    simp only [lift_id, mk_real]
    rw [max_eq_right hK, max_eq_left aleph0_le_continuum]
  have hF : #F = 𝔠 := by rw [FractionRing.cardinalMk, hP]
  have hL : #L = 𝔠 := by
    apply le_antisymm
    · calc #L ≤ max #F ℵ₀ := Algebra.IsAlgebraic.cardinalMk_le_max F L
        _ = 𝔠 := by rw [hF, max_eq_left aleph0_le_continuum]
    · rw [← hF]
      exact mk_le_of_injective (algebraMap F L).injective
  have hlt : ℵ₀ < #L := hL ▸ aleph0_lt_continuum
  obtain ⟨e⟩ := IsAlgClosed.ringEquiv_of_equiv_of_char_eq (K := L) (L := ℂ) 0 hlt
    (Cardinal.eq.1 (hL.trans mk_complex.symm))
  exact ⟨e.toRingHom.comp i⟩

end GlobalTheory.KeyRuleUnique
