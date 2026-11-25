module

public import Formalism.CoboundaryTransfers.Statement

@[expose] public section

namespace Formalism.CoboundaryTransfers

namespace WachMod

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  (W : WachMod B M D)

theorem smulO_eq (c : O) (x : D) : c • x = algebraMap O A c • x := by
  rw [algebraMap_smul]

theorem smulO_mem (c : O) {x : D} (hx : x ∈ W.N) : c • x ∈ W.N := by
  rw [smulO_eq (A := A)]; exact W.N.smul_mem _ hx

theorem qInv_smul (a : A) {y : D} (hy : W.QInv y) : W.QInv (a • y) := by
  simp only [QInv]; rw [smul_comm]; exact W.N.smul_mem a hy

theorem qInv_smulO (c : O) {y : D} (hy : W.QInv y) : W.QInv (c • y) := by
  rw [smulO_eq (A := A)]; exact W.qInv_smul _ hy

theorem xN_smul (a : A) {z : D} (hz : W.XN z) : W.XN (a • z) := by
  obtain ⟨n, hn, rfl⟩ := hz
  exact ⟨a • n, W.N.smul_mem a hn, smul_comm _ _ _⟩

theorem xN_smulO (c : O) {z : D} (hz : W.XN z) : W.XN (c • z) := by
  rw [smulO_eq (A := A)]; exact W.xN_smul _ hz

theorem isOneCochain_smul_of_tower (c : O) {y z : D} (h : W.C1 y z) : W.C1 (c • y) (c • z) :=
  ⟨W.qInv_smulO c h.1, W.xN_smulO c h.2⟩

theorem diffOne_smul_of_tower (c : O) (y z : D) : W.d1 (c • y) (c • z) = c • W.d1 y z := by
  simp only [d1, map_smul, smul_sub]

theorem cocycle_smulO (c : O) {y z : D} (h : W.Cocycle y z) : W.Cocycle (c • y) (c • z) :=
  ⟨W.isOneCochain_smul_of_tower c h.1, by rw [W.diffOne_smul_of_tower, h.2, smul_zero]⟩

end WachMod

end Formalism.CoboundaryTransfers
