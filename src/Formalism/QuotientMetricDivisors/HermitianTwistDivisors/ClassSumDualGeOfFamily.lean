module

public import Formalism.QuotientMetricDivisors.ClassSumDualGeF
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.AuxStatement14
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

namespace Formalism.DivisionValues

namespace ValuationLatticeField

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem mem_valLatF {n : ℕ} {Cl V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (I : (Fin n → K) →ₗ[K] (Cl → V)) (N : Cl → Submodule (𝓞 K) V)
    (x : Fin n → K) : x ∈ valLatF I N ↔ ∀ c, I x c ∈ N c := by
  simp [valLatF, Submodule.mem_pi]

theorem valLatF_mono {n : ℕ} {Cl V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (I : (Fin n → K) →ₗ[K] (Cl → V)) {N N' : Cl → Submodule (𝓞 K) V}
    (h : ∀ c, N c ≤ N' c) : valLatF I N ≤ valLatF I N' := fun x hx =>
  (mem_valLatF I N' x).mpr fun c => h c ((mem_valLatF I N x).mp hx c)

end ValuationLatticeField

open exponent_index_lattice ValuationLatticeField

theorem class_sum_dual_ge_fixed : ClassSumDualGeF := by
  intro K _ _ _ n H Cl _ V _ _ _ _ pair I g hg hCS Nab Del s hDel DG hdvd y hy
  rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
  intro x hx
  rw [LinearMap.map_smul_of_tower, hCS, Finset.smul_sum]
  refine Submodule.sum_mem _ fun c _ => ?_
  obtain ⟨k, hk⟩ := hdvd c
  have hp : (s : 𝓞 K) • pair (I x c) (I y c) ∈ (1 : Submodule (𝓞 K) K) := by
    rw [← LinearMap.map_smul_of_tower]
    exact (Formalism.HermitianLatticesTheory.dualBasic_mem_dual pair (Nab c) _).mp (hDel c _ ((mem_valLatF I Del y).mp hy c)) _
      ((mem_valLatF I Nab x).mp hx c)
  have hg0 : (g c : K) ≠ 0 := by exact_mod_cast (hg c).ne'
  have : ((DG * s : ℕ) : 𝓞 K) • ((g c : K)⁻¹ * pair (I x c) (I y c)) =
      (k : 𝓞 K) • (s : 𝓞 K) • pair (I x c) (I y c) := by
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_natCast, map_natCast, map_natCast, hk]
    push_cast
    field_simp
  rw [this]
  exact Submodule.smul_mem _ _ hp

theorem class_sum_dual_le_fixed : ClassSumDualLeF := by
  classical
  intro K _ _ _ n H Cl _ V _ _ _ _ _ pair hs hn Gam _ _ ρ hiso I hI hCS Nab Del hNab s hDel hstab y hy
  rw [mem_valLatF]
  intro c0
  rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual] at hy
  have hyinv : ∀ c γ, ρ c γ (I y c) = I y c := (hI (I y)).mp ⟨y, rfl⟩
  set N : K := (Fintype.card (Gam c0) : K) with hN
  have hN0 : N ≠ 0 := card_ne (K := K) (Γ := Gam c0)
  let z0 : invSub (ρ c0) := ⟨N⁻¹ • I y c0, (invSub (ρ c0)).smul_mem _ (hyinv c0)⟩
  have hz0 : z0 ∈ Formalism.HermitianLatticesTheory.dual (pair.domRestrict₁₂ (invSub (ρ c0)) (invSub (ρ c0)))
      ((Nab c0).comap ((invSub (ρ c0)).subtype.restrictScalars (𝓞 K))) := by
    rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
    intro x0 hx0
    have hx0' : (x0 : V) ∈ Nab c0 := hx0
    have hinv : ∀ c γ, ρ c γ ((Pi.single c0 (x0 : V) : Cl → V) c) = (Pi.single c0 (x0 : V) : Cl → V) c := by
      intro c γ
      by_cases h : c = c0
      · subst h
        simpa using x0.2 γ
      · simp [Pi.single_eq_of_ne h]
    obtain ⟨x, hx⟩ := (hI _).mpr hinv
    have hxN : x ∈ valLatF I Nab := by
      rw [mem_valLatF, hx]
      intro c
      by_cases h : c = c0
      · subst h
        simpa using hx0'
      · simp [Pi.single_eq_of_ne h]
    have h1 := hy x hxN
    rw [hCS, hx, Finset.sum_eq_single c0 (by
      intro c _ h
      simp [Pi.single_eq_of_ne h]) (by simp)] at h1
    rw [LinearMap.domRestrict₁₂_apply]
    change pair (x0 : V) (N⁻¹ • I y c0) ∈ _
    rw [map_smul, smul_eq_mul]
    simpa using h1
  rw [inv_dual (ρ c0) pair hs hn (hiso c0) (Nab c0) (hNab c0)] at hz0
  obtain ⟨δ, hδ, hδz⟩ := Submodule.mem_map.mp hz0
  have h2 : N⁻¹ • ∑ γ, ρ c0 γ δ = N⁻¹ • I y c0 := by
    have := congrArg (Subtype.val) hδz
    rw [← avg_coe]
    exact this
  have h3 : ∑ γ, ρ c0 γ δ = I y c0 := by
    have := congrArg (fun v => N • v) h2
    simpa [smul_smul, hN0] using this
  rw [LinearMap.map_smul_of_tower, Pi.smul_apply, ← h3, Finset.smul_sum]
  refine Submodule.sum_mem _ fun γ _ => ?_
  rw [← LinearMap.map_smul_of_tower]
  exact hstab c0 γ _ (hDel c0 δ hδ)

namespace ValuationLatticeField

theorem valLatF_isLattice {K : Type} [Field K] [NumberField K] [StarRing K]
    {n : ℕ} {Cl V : Type} [Fintype Cl] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (I : (Fin n → K) →ₗ[K] (Cl → V))
    (hI : Function.Injective I) (N : Cl → Submodule (𝓞 K) V) (hN : ∀ c, Submodule.IsLattice K (N c)) :
    Submodule.IsLattice K (valLatF I N) := by
  classical
  refine ⟨?_, ?_⟩
  · apply Submodule.fg_of_fg_map_injective (I.restrictScalars (𝓞 K)) hI
    exact (Submodule.fg_pi fun c => (hN c).fg).of_le (Submodule.map_comap_le _ _)
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli

theorem valLatF_isFullLattice {K : Type} [Field K] [NumberField K] [StarRing K]
    {n : ℕ} {Cl V : Type} [Fintype Cl] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (I : (Fin n → K) →ₗ[K] (Cl → V))
    (hI : Function.Injective I) (N : Cl → Submodule (𝓞 K) V) (hN : ∀ c, Submodule.IsFullLattice K (N c)) :
    Submodule.IsFullLattice K (valLatF I N) := by
  classical
  refine { toIsLattice := valLatF_isLattice I hI N (fun c => (hN c).toIsLattice)
           span_eq_top := ?_ }
  let M : Submodule (𝓞 K) (Cl → V) := Submodule.pi Set.univ N
  change Submodule.span K (M.comap (I.restrictScalars (𝓞 K)) : Set (Fin n → K)) = ⊤
  apply span_comap_eq_top
  refine eq_top_iff.mpr fun x _ => ?_
  rw [← LinearMap.sum_single_apply (φ := fun _ : Cl => V) (v := x)]
  refine Submodule.sum_mem _ fun c _ => ?_
  let S := Submodule.span K (M : Set (Cl → V))
  have hle : Submodule.span K (N c : Set V) ≤ S.comap (LinearMap.single K (fun _ : Cl => V) c) := by
    refine Submodule.span_le.mpr fun v hv => Submodule.subset_span ?_
    change Pi.single c v ∈ M
    rw [show M = Submodule.pi Set.univ N from rfl, Submodule.mem_pi]
    intro j _
    by_cases hj : j = c
    · subst j
      simpa using hv
    · simp [Pi.single_eq_of_ne hj]
  rw [(hN c).span_eq_top] at hle
  exact hle Submodule.mem_top

end ValuationLatticeField


theorem bounds_class_field_fixed : BoundsIClassF := by
  intro K _ _ _ n' n H' hH hdet E Pr hO Cl _ V _ _ _ _ _ pair hs hn Gam _ _ ρ hiso I hinj hI hCS
    Nab Del hNab s hDel hle hstab G0 _ r c G he hc hr
  have hA := valLatF_isFullLattice I hinj Nab hNab
  have h1 := class_sum_dual_le_fixed K n' H' Cl V pair hs hn Gam ρ hiso I hI hCS Nab Del hNab s hDel hstab
  have h2 : valLatF I Del ≤ valLatF I Nab := valLatF_mono I hle
  have h3 := projection_integral K n' G0 r c G hc (valLatF I Del) hr
  rw [← he] at h3
  exact ⟨hA, divisor_bounds_first K n' n H' hH hdet E Pr hO _ _ hA s h1 G fun x hx => h2 (h3 x hx)⟩

theorem bounds_fourth_class_fixed : BoundsIVClassF := by
  intro K _ _ _ n d H hH hdet E Pr hO Cl _ V _ _ _ _ pair I g hinj hg hCS Nab Del hNab s hs0 hDel
    DG hDG hdvd w ϖ J hϖ hJ
  have hA := valLatF_isFullLattice I hinj Nab hNab
  have h1 := class_sum_dual_ge_fixed K n H Cl V pair I g hg hCS Nab Del s hDel DG hdvd
  have h := bounds_fourth K n d H hH hdet E Pr hO _ _ hA (DG * s) (Nat.mul_pos hDG hs0) h1 w ϖ J hϖ hJ
  have hG' : (DG : K) ≠ 0 := by exact_mod_cast hDG.ne'
  have hs' : (s : K) ≠ 0 := by exact_mod_cast hs0.ne'
  have h4 := h.2.2.2
  rw [Nat.cast_mul, ValuationRepresentative.vw_mul w _ _ hG' hs', ← add_assoc] at h4
  exact ⟨h.1, h4⟩

end Formalism.DivisionValues
