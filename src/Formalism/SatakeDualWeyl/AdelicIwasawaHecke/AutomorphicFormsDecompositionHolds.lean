module

public import Formalism.SatakeDualWeyl.Statement

@[expose] public section

namespace Formalism.UG.P

open Formalism.UG

section Rep

variable {G : Type} [Group G] (Γ K : Subgroup G)

theorem exists_rep (s : ClassSet Γ K → G) (hs : ∀ c, DoubleCoset.mk Γ K (s c) = c) (g : G) :
    ∃ p : Γ × K, g = (p.1 : G) * s (DoubleCoset.mk Γ K g) * (p.2 : G) := by
  have h := (@DoubleCoset.eq _ _ Γ K (s (DoubleCoset.mk Γ K g)) g).1 (hs _)
  obtain ⟨a, ha, b, hb, hab⟩ := h
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩

variable {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]

end Rep

end Formalism.UG.P
