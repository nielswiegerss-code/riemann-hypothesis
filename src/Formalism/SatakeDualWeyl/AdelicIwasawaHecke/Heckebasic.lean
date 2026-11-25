module

public import Formalism.SatakeDualWeyl.Statement

@[expose] public section

open Classical

namespace Formalism.UG.P

open Formalism.UG

section Generic

variable {G : Type} [Group G]

theorem mem_dc_iff (K : Subgroup G) (g x : G) :
    x ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) ↔
      ∃ a : K, ∃ b : K, x = (a : G) * g * b := by
  rw [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, a.2, b, b.2, rfl⟩

theorem mem_dc_one (K : Subgroup G) (x : G) :
    x ∈ DoubleCoset.doubleCoset (1 : G) (K : Set G) (K : Set G) ↔ x ∈ K := by
  rw [mem_dc_iff]
  constructor
  · rintro ⟨a, b, rfl⟩
    rw [mul_one]
    exact K.mul_mem a.2 b.2
  · intro hx
    exact ⟨⟨x, hx⟩, 1, by simp⟩

theorem ind_biInv (k : Type) [CommRing k] (K : Subgroup G) (T : Set G)
    (hT : ∀ a b : K, ∀ x : G, x ∈ T → (a : G) * x * b ∈ T) :
    IsBiInv K (T.indicator (1 : G → k)) := by
  unfold IsBiInv
  intro a b x
  by_cases hx : x ∈ T
  · simp [hx, hT a b x hx]
  · have h' : (a : G) * x * b ∉ T := by
      intro h
      apply hx
      have := hT a⁻¹ b⁻¹ _ h
      simpa [mul_assoc] using this
    simp [hx, h']

theorem dc_stable (K : Subgroup G) (g : G) (a b : K) (x : G)
    (hx : x ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G)) :
    (a : G) * x * b ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) := by
  rw [mem_dc_iff] at hx ⊢
  obtain ⟨c, d, rfl⟩ := hx
  exact ⟨a * c, d * b, by simp [mul_assoc]⟩

theorem mem_hecke_iff (k : Type) [CommRing k] (K : Subgroup G) (f : G → k) :
    f ∈ Hecke k K ↔ IsBiInv K f ∧ FinDosetSupp K f := Iff.rfl

theorem dosetInd_of_mem (k : Type) [CommRing k] (K : Subgroup G) (g x : G)
    (hx : x ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G)) : dosetInd k K g x = 1 := by
  simp [dosetInd, hx]

theorem dosetInd_of_not_mem (k : Type) [CommRing k] (K : Subgroup G) (g x : G)
    (hx : x ∉ DoubleCoset.doubleCoset g (K : Set G) (K : Set G)) : dosetInd k K g x = 0 := by
  simp [dosetInd, hx]

end Generic

theorem double_coset_indicator_mem : Formalism.UG.DosetIndMem := by
  unfold Formalism.UG.DosetIndMem
  intro G _ K k _ g
  rw [mem_hecke_iff]
  refine ⟨ind_biInv k K _ (fun a b x hx => dc_stable K g a b x hx), ?_⟩
  refine ⟨{g}, fun x hx => ⟨g, Finset.mem_singleton_self g, (mem_dc_iff K g x).1 ?_⟩⟩
  by_contra h
  exact hx (dosetInd_of_not_mem k K g x h)

end Formalism.UG.P
