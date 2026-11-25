module

public import Formalism.HermitianLattices.NeighbourConstruct
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic

@[expose] public section

open nonZeroDivisors

namespace Formalism.HermitianLatticesTheory

section Gen

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem neighbourConstruct_mem_inv {P : Ideal R} {a : K} :
    a ∈ invIdeal (K := K) P ↔ ∀ p ∈ P, algebraMap R K p * a ∈ Set.range (algebraMap R K) := by
  unfold invIdeal
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulLeft_apply, Submodule.mem_one]
  rfl

theorem neighbourConstruct_mem_span {P : Ideal R} {x z : V} :
    z ∈ Submodule.span R {z | ∃ a ∈ invIdeal (K := K) P, z = a • x} ↔
      ∃ a ∈ invIdeal (K := K) P, z = a • x := by
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add y y' _ _ h1 h2 =>
      obtain ⟨a, ha, rfl⟩ := h1
      obtain ⟨b, hb, rfl⟩ := h2
      exact ⟨a + b, Submodule.add_mem _ ha hb, by rw [add_smul]⟩
    | smul r y _ h1 =>
      obtain ⟨a, ha, rfl⟩ := h1
      refine ⟨r • a, Submodule.smul_mem _ r ha, ?_⟩
      rw [smul_assoc]
  · intro hz
    exact Submodule.subset_span hz

end Gen

section DedekindLFunctions

variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem neighbourConstruct_one_mem (P : Ideal R) (hP0 : P ≠ ⊥) :
    (1 : K) ∈ Submodule.map (Algebra.linearMap R K) P * invIdeal (K := K) P := by
  have e := FractionalIdeal.coe_ideal_mul_inv (K := K) P hP0
  have e2 : ((P : FractionalIdeal R⁰ K) : Submodule R K) *
      (((P : FractionalIdeal R⁰ K)⁻¹ : FractionalIdeal R⁰ K) : Submodule R K) = 1 := by
    rw [← FractionalIdeal.coe_mul, e, FractionalIdeal.coe_one]
  have h1 : (1 : K) ∈ ((P : FractionalIdeal R⁰ K) : Submodule R K) *
      (((P : FractionalIdeal R⁰ K)⁻¹ : FractionalIdeal R⁰ K) : Submodule R K) := by
    rw [e2]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  have hne : (P : FractionalIdeal R⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hP0
  refine (mul_le_mul' ?_ ?_ : _ ≤ Submodule.map (Algebra.linearMap R K) P * invIdeal (K := K) P) h1
  · rw [FractionalIdeal.coe_coeIdeal]; exact le_rfl
  · intro a ha
    rw [neighbourConstruct_mem_inv]
    intro p hp
    have := (FractionalIdeal.mem_inv_iff hne).mp ha (algebraMap R K p)
      (FractionalIdeal.mem_coeIdeal_of_mem _ hp)
    rw [mul_comm]
    exact (FractionalIdeal.mem_one_iff _).mp this

theorem neighbourConstruct_key (P : Ideal R) (hP0 : P ≠ ⊥) (L : Submodule R V) (x : V)
    (H : ∀ a ∈ invIdeal (K := K) P, a • x ∈ L) : x ∈ P • L := by
  have h1 := neighbourConstruct_one_mem (K := K) P hP0
  have : ((1 : K) • x) ∈ P • L := by
    refine Submodule.mul_induction_on (C := fun k => k • x ∈ P • L) h1 ?_ ?_
    · intro m hm n hn
      obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hm
      rw [Algebra.linearMap_apply, mul_smul, algebraMap_smul]
      exact Submodule.smul_mem_smul hp (H n hn)
    · intro a b ha hb
      rw [add_smul]; exact Submodule.add_mem _ ha hb
  simpa using this

end DedekindLFunctions

end Formalism.HermitianLatticesTheory
