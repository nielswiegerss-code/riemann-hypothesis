module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapNeZeroOfMemHcompl
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteDimensionalOfOrtho

@[expose] public section

open NumberField Module Matrix

namespace Formalism.HermitianLattices.Ext.L3.LocF

open Formalism.HermitianLattices.Ext.L3.WA

section Units

variable {K : Type*} [Field K] {S : Subring K}

theorem isUnitIn_mul {a b : K} (ha : IsUnitIn S a) (hb : IsUnitIn S b) : IsUnitIn S (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, S.mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact S.mul_mem ha.2.2 hb.2.2⟩

theorem isUnitIn_one : IsUnitIn S (1 : K) :=
  ⟨one_ne_zero, S.one_mem, by rw [inv_one]; exact S.one_mem⟩

theorem isUnitIn_prod {ι : Type*} (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, IsUnitIn S (f i)) :
    IsUnitIn S (∏ i ∈ s, f i) :=
  Finset.prod_induction f (IsUnitIn S) (fun _ _ => isUnitIn_mul) isUnitIn_one hf

end Units

section Ring

variable {K : Type} [Field K] [NumberField K] [StarRing K]

private lemma hcompl_unit_property_of_isPrime {p : Ideal (𝓞 K)} (hp : p.IsPrime) {N S : 𝓞 K} (hS : S ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p)
    (hN : N ∉ p) (hfix : star (algebraMap (𝓞 K) K N / algebraMap (𝓞 K) K S) =
      algebraMap (𝓞 K) K N / algebraMap (𝓞 K) K S) :
    IsUnitIn (locRing p) (algebraMap (𝓞 K) K N / algebraMap (𝓞 K) K S) := by
  have hS0 := algebraMap_ne_zero_of_mem_hcompl hp hS
  have hS'p := ((mem_hcompl_iff hp S).1 hS).2
  rw [mem_conjIdeal_iff] at hS'p
  rw [star_div₀, div_eq_div_iff (star_ne_zero.2 hS0) hS0] at hfix
  have key : conjO K N * S = N * conjO K S := IsFractionRing.injective (𝓞 K) K (by
    rw [map_mul, map_mul, algebraMap_conjO, algebraMap_conjO, hfix])
  refine (isUnitIn_div_iff hp N hS).2 ((mem_hcompl_iff hp N).2 ⟨hN, fun h => ?_⟩)
  rw [mem_conjIdeal_iff] at h
  exact (hp.mem_or_mem (key ▸ p.mul_mem_right S h)).elim hN hS'p

theorem fixed_nonunit {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K} (ha : a ∈ locRing p)
    (hfix : star a = a) (hnu : ¬ IsUnitIn (locRing p) a) :
    ∃ r ∈ p, ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p,
      a = algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s := by
  obtain ⟨t, s, hs, rfl⟩ := (mem_locR_iff hp a).1 ha
  refine ⟨t, ?_, s, hs, rfl⟩
  by_contra htp
  exact hnu (hcompl_unit_property_of_isPrime hp hs htp hfix)

theorem locRing_local {p : Ideal (𝓞 K)} (hp : p.IsPrime) :
    ∀ a ∈ locRing p, ∀ b ∈ locRing p, star a = a → star b = b → ¬ IsUnitIn (locRing p) a →
      ¬ IsUnitIn (locRing p) b → IsUnitIn (locRing p) (a + b + 1) := by
  intro a ha b hb hfa hfb hna hnb
  obtain ⟨r1, hr1, s1, hs1, rfl⟩ := fixed_nonunit hp ha hfa hna
  obtain ⟨r2, hr2, s2, hs2, rfl⟩ := fixed_nonunit hp hb hfb hnb
  have h1 := algebraMap_ne_zero_of_mem_hcompl hp hs1
  have h2 := algebraMap_ne_zero_of_mem_hcompl hp hs2
  have hS : s1 * s2 ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := Submonoid.mul_mem _ hs1 hs2
  have hN : r1 * s2 + r2 * s1 + s1 * s2 ∉ p := by
    intro h
    have : s1 * s2 ∈ p := by
      have := p.sub_mem h (p.add_mem (p.mul_mem_right s2 hr1) (p.mul_mem_right s1 hr2))
      simpa using this
    exact ((mem_hcompl_iff hp _).1 hS).1 this
  have e : algebraMap (𝓞 K) K r1 / algebraMap (𝓞 K) K s1 + algebraMap (𝓞 K) K r2 / algebraMap (𝓞 K) K s2 + 1 =
      algebraMap (𝓞 K) K (r1 * s2 + r2 * s1 + s1 * s2) / algebraMap (𝓞 K) K (s1 * s2) := by
    simp only [map_add (f := _), map_mul]
    field_simp
  have hf := congrArg id (show star (algebraMap (𝓞 K) K r1 / algebraMap (𝓞 K) K s1 +
      algebraMap (𝓞 K) K r2 / algebraMap (𝓞 K) K s2 + 1) = _ by rw [star_add, star_add, star_one, hfa, hfb])
  rw [e] at hf ⊢
  exact hcompl_unit_property_of_isPrime hp hS hN hf

theorem isUnitIn_algebraMap_iff {p : Ideal (𝓞 K)} (hp : p.IsPrime) (r : 𝓞 K) :
    IsUnitIn (locRing p) (algebraMap (𝓞 K) K r) ↔ r ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
  simpa only [map_one, div_one] using isUnitIn_div_iff hp r (one_mem (Formalism.HermitianLatticesTheory.hcompl (K := K) p))

end Ring

section Gram

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ}

theorem gram_mulVec (x : Fin n → V) (c : Fin n → K) (i : Fin n) :
    ((Matrix.of fun i j => h (x i) (x j)) *ᵥ c) i = h (x i) (∑ j, c j • x j) := by

  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, map_sum, map_smul, smul_eq_mul, mul_comm]

theorem linearIndependent_of_gram_det_ne_zero (x : Fin n → V)
    (hdet : (Matrix.of fun i j => h (x i) (x j)).det ≠ 0) : LinearIndependent K x := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hG : (Matrix.of fun i j => h (x i) (x j)) *ᵥ c = 0 := by
    funext i
    rw [gram_mulVec h x c i, hc, map_zero, Pi.zero_apply]
  exact fun i => congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hG) i

theorem gram_det_ne_zero (hd : ∀ x, h x x = 0 → x = 0) (x : Fin n → V)
    (hli : LinearIndependent K x) : (Matrix.of fun i j => h (x i) (x j)).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have e : ∀ i, h (x i) (∑ j, v j • x j) = 0 := fun i => by
    rw [← gram_mulVec h x v i, hv, Pi.zero_apply]
  have e' : ∀ i, h (v i • x i) (∑ j, v j • x j) = 0 := fun i => by
    rw [map_smulₛₗ, LinearMap.smul_apply, e, smul_zero]
  have hy : h (∑ j, v j • x j) (∑ j, v j • x j) = 0 := by
    have hs : h (∑ j, v j • x j) = ∑ j, h (v j • x j) := map_sum h _ _
    rw [hs, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun i _ => e' i
  have := Fintype.linearIndependent_iff.mp hli v (hd _ hy)
  exact hv0 (funext this)

theorem star_gram_det (hs : h.IsSymm) (x : Fin n → V) :
    star (Matrix.of fun i j => h (x i) (x j)).det = (Matrix.of fun i j => h (x i) (x j)).det := by
  rw [← Matrix.det_conjTranspose]
  congr 1
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
  first
  | exact hs.eq (x j) (x i)

end Gram

section Cramer

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ}

theorem det_smul_mem {L : Submodule (𝓞 K) V} (x : Fin n → V) (hx : ∀ i, x i ∈ L)
    (hspan : Submodule.span K (Set.range x) = ⊤) (g : Matrix (Fin n) (Fin n) (𝓞 K))
    (hg : ∀ i j, algebraMap (𝓞 K) K (g i j) = h (x i) (x j)) (y : V)
    (hy : ∀ i, h (x i) y ∈ (1 : Submodule (𝓞 K) K)) : g.det • y ∈ L := by
  have hy' : y ∈ Submodule.span K (Set.range x) := by rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy'
  choose β hβ using fun i => Submodule.mem_one.mp (hy i)
  set G := Matrix.of fun i j => h (x i) (x j) with hGdef
  have hGg : (algebraMap (𝓞 K) K).mapMatrix g = G := by
    ext i j
    simp [RingHom.mapMatrix_apply, hg, hGdef]
  have hGc : G *ᵥ c = fun i => algebraMap (𝓞 K) K (β i) := by
    funext i
    rw [hGdef, gram_mulVec h x c i, hc, hβ]

  have hdetc : G.det • c = fun j => algebraMap (𝓞 K) K ((g.adjugate *ᵥ β) j) := by
    funext j
    have h1 : G.det • c = G.adjugate *ᵥ (G *ᵥ c) := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul]
      first
      | rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [h1, hGc, RingHom.map_mulVec, ← hGg, ← RingHom.map_adjugate]
    rfl
  have hdet : algebraMap (𝓞 K) K g.det = G.det := by rw [RingHom.map_det, hGg]
  rw [← algebraMap_smul K g.det y, hdet, ← hc, Finset.smul_sum]
  have hj : ∀ j, G.det • (c j • x j) = (g.adjugate *ᵥ β) j • x j := by
    intro j
    have := congrFun hdetc j
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [smul_smul, this, algebraMap_smul]
  rw [Finset.sum_congr rfl fun j _ => hj j]
  exact L.sum_mem fun j _ => L.smul_mem _ (hx j)

end Cramer

end Formalism.HermitianLattices.Ext.L3.LocF
