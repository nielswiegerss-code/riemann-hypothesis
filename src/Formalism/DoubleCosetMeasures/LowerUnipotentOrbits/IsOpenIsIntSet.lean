module

public import Formalism.DoubleCosetMeasures.Statement
import Mathlib.Topology.Algebra.Group.Units

@[expose] public section

open MeasureTheory Matrix

namespace Formalism.DoubleCosetMeasures.P

open Formalism.DoubleCosetMeasures

section SlopeTestRemainingChoices

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

theorem isOpen_isInt_set (R : Subring K) (hR : IsOpen (R : Set K)) (n : ℕ) :
    IsOpen {g : GL (Fin n) K | IsInt R (g : Matrix (Fin n) (Fin n) K) ∧
      IsInt R ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)} := by
  have hset : {g : GL (Fin n) K | IsInt R (g : Matrix (Fin n) (Fin n) K) ∧
      IsInt R ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)} =
      (⋂ a, ⋂ b, {g : GL (Fin n) K | (g : Matrix (Fin n) (Fin n) K) a b ∈ R}) ∩
      (⋂ a, ⋂ b, {g : GL (Fin n) K | ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b ∈ R}) := by
    ext g
    simp [IsInt, Set.mem_iInter]
  rw [hset]
  apply IsOpen.inter
  · refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_
    exact hR.preimage (Units.continuous_val.matrix_elem a b)
  · refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_
    exact hR.preimage (Units.continuous_coe_inv.matrix_elem a b)

theorem isOpen_intSub (R : Subring K) (hR : IsOpen (R : Set K)) {n : ℕ}
    (H : Subgroup (GL (Fin n) K)) : IsOpen (intSub R H : Set H) := by
  exact (isOpen_isInt_set R hR n).preimage continuous_subtype_val

end SlopeTestRemainingChoices

theorem sLow_mem {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (x : Matrix (Fin n) (Fin n) K)
    (hx : IsInt R x) : sLow x ∈ R := by
  unfold sLow
  refine R.sum_mem fun j _ => ?_
  split_ifs
  · exact hx _ _
  · exact R.zero_mem

theorem sUp_mem {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (x : Matrix (Fin n) (Fin n) K)
    (hx : IsInt R x) : sUp x ∈ R := by
  unfold sUp
  refine R.sum_mem fun j _ => ?_
  split_ifs
  · exact hx _ _
  · exact R.zero_mem

theorem phi_inv (hIntInv : IntInv) (hIsoInv : IsoInv) (hSA : SimpleAdd)
    {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (s : List ℕ) (t : ℕ → Kˣ) (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1)
    (C : Type) [AddCommGroup C] [Module R C] (e : C) (lam : C →ₗ[R] KR R) :
    ∀ a ∈ intSub R (lowW K s t), ∀ b ∈ intSub R (upUniG K s.sum), ∀ x : lowW K s t,
      ∀ y : upUniG K s.sum, phi R s t ψ C e lam (a * x, y * b) = phi R s t ψ C e lam (x, y) := by
  intro a ha b hb x y
  have haI : IsInt R (((a : GL (Fin s.sum) K)) : Matrix (Fin s.sum) (Fin s.sum) K) := ha.1
  have hbI : IsInt R (((b : GL (Fin s.sum) K)) : Matrix (Fin s.sum) (Fin s.sum) K) := hb.1
  have haL : IsLowUni (((a : GL (Fin s.sum) K)) : Matrix (Fin s.sum) (Fin s.sum) K) := a.2.1
  have hxL : IsLowUni (((x : GL (Fin s.sum) K)) : Matrix (Fin s.sum) (Fin s.sum) K) := x.2.1
  have hbU : IsUpUni (((b : GL (Fin s.sum) K)) : Matrix (Fin s.sum) (Fin s.sum) K) := b.2
  have hyU : IsUpUni (((y : GL (Fin s.sum) K)) : Matrix (Fin s.sum) (Fin s.sum) K) := y.2
  unfold phi
  simp only [Subgroup.coe_mul, Units.val_mul]
  have hi := hIntInv K R s.sum _ _
    (((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t *
      ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) haL hbU haI hbI
  have hc := hIsoInv K R s.sum _ _
    (((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t *
      ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) haL hbU haI hbI C e lam
  have hi' : IsInt R (((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) *
      ((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t *
      (((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) *
       ((b : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K))) ↔
      IsInt R (((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t *
       ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) := by
    simpa only [mul_assoc] using hi
  have heq : (((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) *
      ((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t *
      (((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) *
       ((b : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K))) =
      ((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) *
      (((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t *
       ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) *
      ((b : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) := by simp only [mul_assoc]
  have hc' := (congrArg (fun z => Nat.card (isoSet R z C e lam)) heq).trans hc
  simp only [hi', hc', (hSA K s.sum _ _).1 haL hxL, (hSA K s.sum _ _).2 hyU hbU]
  have hpa : ψ (sLow ((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) = 1 := hψ _ (sLow_mem R _ haI)
  have hpb : ψ (sUp ((b : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) = 1 := hψ _ (sUp_mem R _ hbI)
  rw [show sLow ((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + sLow ((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + (sUp ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + sUp ((b : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) =
      (sLow ((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + sUp ((b : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) + (sLow ((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + sUp ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) by abel]
  simp only [AddChar.map_add_eq_mul, hpa, hpb, one_mul]
  split_ifs with h h <;> simp_all

theorem bbFinite_of : IntTwoSided → IntInv → IsoInv → SimpleAdd → BBFinite := by
  intro hTS hII hIso hSA K _ _ _ R hR s t ψ hψ μ₁ μ₂ _ _ _ _ C _ _ e lam hcs
  have h := hTS (lowW K s t) (upUniG K s.sum) μ₁ μ₂ (intSub R (lowW K s t))
    (intSub R (upUniG K s.sum)) (isOpen_intSub R hR _) (isOpen_intSub R hR _) ℂ
    (phi R s t ψ C e lam) (phi_inv hII hIso hSA R s t ψ hψ C e lam) hcs
  refine ⟨h.1, ?_⟩
  rw [BB, h.2]
  congr 1

theorem bbNorm_of : BBFinite → BBNorm := by
  intro hBB K _ _ _ R hR s t ψ hψ μ₁ μ₂ _ _ _ _ h1 h2 C _ _ e lam hcs
  rw [(hBB K R hR s t ψ hψ μ₁ μ₂ C e lam hcs).2, h1, h2]
  simp

end Formalism.DoubleCosetMeasures.P
