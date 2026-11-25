module

public import Formalism.LatticeSlopes.Statement
public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram
public import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe
public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolPos
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Mathlib.LinearAlgebra.FreeModule.PID

@[expose] public section

open Module Submodule

namespace Formalism.F

theorem linearIndependent_coe_basis''' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] {ι : Type*} [Fintype ι]
    (b : Basis ι ℤ L) : LinearIndependent ℝ (fun i => (b i : E)) :=
  linearIndependent_coe_basis L b

theorem discreteTopology_span_range_of_linearIndependent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] (c : ι → E) (hc : LinearIndependent ℝ c) :
    DiscreteTopology (span ℤ (Set.range c)) := by
  classical
  let φ : (ι → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ c
  have hker : LinearMap.ker φ = ⊥ :=
    LinearMap.ker_eq_bot'.mpr fun r hr => funext (Fintype.linearIndependent_iff.1 hc r hr)
  obtain ⟨K, hK, hφ⟩ := LinearMap.exists_antilipschitzWith φ hker
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have key : ∀ x ∈ span ℤ (Set.range c), x ≠ 0 → (K : ℝ)⁻¹ ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨n, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
    have hφn : φ (fun i => (n i : ℝ)) = ∑ i, n i • c i :=
      Finset.sum_congr rfl fun i _ => Int.cast_smul_eq_zsmul ℝ (n i) (c i)
    obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
      by_contra hcon; push Not at hcon; exact hx0 (by simp [hcon])
    have h1 : (1 : ℝ) ≤ ‖(fun i => (n i : ℝ))‖ :=
      (by exact_mod_cast Int.one_le_abs hi : (1 : ℝ) ≤ |(n i : ℝ)|).trans
        ((Real.norm_eq_abs _).symm.trans_le (norm_le_pi_norm (fun j => (n j : ℝ)) i))
    have h2 := hφ.le_mul_dist (fun i => (n i : ℝ)) 0
    rw [dist_zero_right, map_zero, dist_zero_right, hφn] at h2
    rw [inv_eq_one_div, div_le_iff₀ hKpos]
    nlinarith
  apply discreteTopology_of_isOpen_singleton_zero
  refine isOpen_induced_iff.mpr ⟨Metric.ball 0 (K : ℝ)⁻¹, Metric.isOpen_ball, ?_⟩
  ext y
  simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, Set.mem_singleton_iff]
  refine ⟨fun h => by_contra fun hne => absurd (key y y.2 (fun h0 => hne (Subtype.ext h0))) (not_le.mpr h),
    fun h => by simpa [h] using inv_pos.mpr hKpos⟩

theorem span_range_coe_basis' {E : Type*} [AddCommGroup E] (L : Submodule ℤ E) {ι : Type*}
    (b : Basis ι ℤ L) : span ℤ (Set.range (fun i => (b i : E))) = L := by
  rw [show (Set.range fun i => (b i : E)) = L.subtype '' Set.range b from Set.range_comp _ _,
    Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem degree_quotient : DegQuot := by
  intro E _ _ _ L N hL hsat
  classical
  obtain ⟨hNL, hsat'⟩ := hsat
  have := hL
  have : DiscreteTopology N := discreteTopology_of_le hNL
  let W : Submodule ℝ E := span ℝ (N : Set E)
  let P : E →L[ℝ] E := Wᗮ.starProjection
  have hPmem : ∀ x : E, P x ∈ Wᗮ := fun x => Submodule.starProjection_apply_mem _ x
  have hPsub : ∀ x : E, x - P x ∈ W := fun x => by
    have h := Submodule.sub_starProjection_mem_orthogonal (K := Wᗮ) x
    rwa [Submodule.orthogonal_orthogonal] at h
  have hPW : ∀ x ∈ W, P x = 0 := fun x hx =>
    (Submodule.starProjection_apply_eq_zero_iff Wᗮ).mpr ((Submodule.orthogonal_orthogonal W).symm ▸ hx)
  have hNW : ∀ x ∈ N, x ∈ W := fun x hx => Submodule.subset_span hx
  have hker : ∀ x ∈ L, P x = 0 → x ∈ N := fun x hx h0 =>
    hsat' x hx (by simpa [h0] using hPsub x)
  set Q := quot L N
  have hQmem : ∀ y : E, y ∈ Q ↔ ∃ x ∈ L, P x = y := fun _ => Submodule.mem_map
  have : Module.Finite ℤ Q := Module.Finite.map L _
  have : Module.IsTorsionFree ℤ Q := Module.IsTorsionFree.mk fun r hr x y hxy => by
    apply Subtype.ext
    have h : (r : ℝ) • (x : E) = (r : ℝ) • (y : E) := by
      simpa [Int.cast_smul_eq_zsmul] using congrArg Subtype.val hxy
    exact smul_right_injective E (Int.cast_ne_zero.mpr hr.ne_zero) h
  have : Module.Free ℤ Q := Module.free_of_finite_type_torsion_free'
  let eQ := Module.Free.chooseBasis ℤ Q
  let bN := Module.Free.chooseBasis ℤ N
  choose ℓ hℓL hℓP using fun j => (hQmem _).1 (eQ j).2
  let v : Module.Free.ChooseBasisIndex ℤ N ⊕ Module.Free.ChooseBasisIndex ℤ Q → L :=
    Sum.elim (fun i => ⟨(bN i : E), hNL (bN i).2⟩) (fun j => ⟨ℓ j, hℓL j⟩)
  have hvE : ∀ k, ((v k : L) : E) = Sum.elim (fun i => (bN i : E)) ℓ k := by rintro (i | j) <;> rfl
  have hli : LinearIndependent ℤ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hgE : ∑ i, g (Sum.inl i) • (bN i : E) + ∑ j, g (Sum.inr j) • ℓ j = 0 := by
      simpa [Fintype.sum_sum_type, v] using congrArg (fun z : L => (z : E)) hg
    have hPg : ∑ j, g (Sum.inr j) • (eQ j : E) = 0 := by
      have h := congrArg P hgE
      simp only [map_add, map_sum, map_zsmul, map_zero, hℓP] at h
      have h0 : ∑ i, g (Sum.inl i) • P (bN i : E) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hPW _ (hNW _ (bN i).2), smul_zero]
      rwa [h0, zero_add] at h
    have hQz : ∀ j, g (Sum.inr j) = 0 :=
      Fintype.linearIndependent_iff.1 eQ.linearIndependent _ (Subtype.ext (by simpa using hPg))
    have hNz : ∀ i, g (Sum.inl i) = 0 :=
      Fintype.linearIndependent_iff.1 bN.linearIndependent _
        (Subtype.ext (by simpa [hQz] using hgE))
    rintro (i | j)
    · exact hNz i
    · exact hQz j
  have hsp : ⊤ ≤ span ℤ (Set.range v) := by
    rintro ⟨x, hx⟩ -
    have hr := congrArg (fun z : Q => (z : E)) (eQ.sum_repr ⟨P x, (hQmem _).2 ⟨x, hx, rfl⟩⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hr
    set r := eQ.repr ⟨P x, (hQmem _).2 ⟨x, hx, rfl⟩⟩
    have hy : x - ∑ j, r j • ℓ j ∈ N := hker _
      (L.sub_mem hx (L.sum_mem fun j _ => L.smul_mem _ (hℓL j)))
      (by simp [map_sub, map_sum, map_zsmul, hℓP, hr])
    have hs := congrArg (fun z : N => (z : E)) (bN.sum_repr ⟨_, hy⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hs
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨Sum.elim (bN.repr ⟨_, hy⟩) r, Subtype.ext ?_⟩
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Submodule.coe_add,
      Submodule.coe_sum, Submodule.coe_smul, v]
    rw [hs]; abel
  let cB := Basis.mk hli hsp
  have hcB : (fun k => ((cB k : L) : E)) = Sum.elim (fun i => (bN i : E)) ℓ :=
    funext fun k => by rw [Basis.mk_apply, hvE]
  have hindR : LinearIndependent ℝ (Sum.elim (fun i => (bN i : E)) ℓ) :=
    hcB ▸ linearIndependent_coe_basis L cB
  have hWspan : W = span ℝ (Set.range fun i => (bN i : E)) := by
    rw [← Submodule.span_span_of_tower ℤ ℝ, span_range_coe_basis' N bN]
  have heQ : LinearIndependent ℝ (fun j => (eQ j : E)) := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have hmem : ∑ j, a j • ℓ j ∈ span ℝ (Set.range fun i => (bN i : E)) := by
      have h0 : P (∑ j, a j • ℓ j) = 0 := by simpa [map_sum, map_smul, hℓP] using ha
      simpa [hWspan, h0] using hPsub (∑ j, a j • ℓ j)
    obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
    have hrel : ∑ k, (Sum.elim (fun i => -β i) a k) • Sum.elim (fun i => (bN i : E)) ℓ k = 0 := by
      simp [Fintype.sum_sum_type, hβ]
    exact fun j => Fintype.linearIndependent_iff.1 hindR _ hrel (Sum.inr j)
  have hQd : DiscreteTopology Q := by
    have h := discreteTopology_span_range_of_linearIndependent (fun j => (eQ j : E)) heQ
    rwa [span_range_coe_basis' Q eQ] at h
  have hrk : rk L = rk N + rk Q := by
    simp only [rk, Module.finrank_eq_card_basis cB, Module.finrank_eq_card_basis bN,
      Module.finrank_eq_card_basis eQ, Fintype.card_sum]
  have hα' : ∀ j, ∃ α : Module.Free.ChooseBasisIndex ℤ N → ℝ,
      ∑ i, α i • (bN i : E) = ℓ j - (eQ j : E) := fun j =>
    (Submodule.mem_span_range_iff_exists_fun ℝ).1 (by rw [← hWspan, ← hℓP j]; exact hPsub (ℓ j))
  choose α hα using hα'
  let v2 := Sum.elim (fun i => (bN i : E)) (fun j => (eQ j : E))
  let M : Matrix (Module.Free.ChooseBasisIndex ℤ N ⊕ Module.Free.ChooseBasisIndex ℤ Q)
      (Module.Free.ChooseBasisIndex ℤ N ⊕ Module.Free.ChooseBasisIndex ℤ Q) ℝ :=
    Matrix.fromBlocks 1 (Matrix.of fun i j => α j i) 0 1
  have hcomb : (fun k => ((cB k : L) : E)) = fun k => ∑ k', M k' k • v2 k' := by
    rw [hcB]; funext k; cases k with
    | inl i0 => simp [M, v2, Fintype.sum_sum_type, Matrix.one_apply]
    | inr j0 => simp [M, v2, Fintype.sum_sum_type, Matrix.one_apply, hα]
  have hgram : Matrix.gram ℝ v2 = Matrix.fromBlocks (Matrix.gram ℝ fun i => (bN i : E)) 0 0
      (Matrix.gram ℝ fun j => (eQ j : E)) := by
    ext (i | j) (i' | j') <;> simp only [Matrix.gram_apply, v2, Sum.elim_inl, Sum.elim_inr,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
    · exact Submodule.inner_right_of_mem_orthogonal (hNW _ (bN i).2) (hℓP j' ▸ hPmem _)
    · exact Submodule.inner_left_of_mem_orthogonal (hNW _ (bN i').2) (hℓP j ▸ hPmem _)
  have hdet : (Matrix.gram ℝ fun k => ((cB k : L) : E)).det =
      (Matrix.gram ℝ fun i => (bN i : E)).det * (Matrix.gram ℝ fun j => (eQ j : E)).det := by
    rw [hcomb, gram_sum_smul_eq_transpose_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      show M.det = 1 by simp [M], hgram, Matrix.det_fromBlocks_zero₂₁]
    ring
  have hposN : 0 < (Matrix.gram ℝ fun i => (bN i : E)).det :=
    (Matrix.posDef_gram_of_linearIndependent (linearIndependent_coe_basis N bN)).det_pos
  have hposQ : 0 < (Matrix.gram ℝ fun j => (eQ j : E)).det :=
    (Matrix.posDef_gram_of_linearIndependent heQ).det_pos
  refine ⟨hQd, hrk, ?_⟩
  unfold deg
  rw [covol_eq_gram E L _ cB, covol_eq_gram E N _ bN, covol_eq_gram E Q _ eQ, hdet,
    Real.sqrt_mul hposN.le, Real.log_mul (Real.sqrt_pos.2 hposN).ne' (Real.sqrt_pos.2 hposQ).ne']
  ring

end Formalism.F
