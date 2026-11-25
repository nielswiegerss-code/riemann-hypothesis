module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.LettersFreeOfRank
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.WachLettersFree

@[expose] public section

namespace GlobalTheory.WachLettersCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

attribute [local instance] letterModule

theorem mul_letE (i : ZMod n) (a : LetA O n) : a * letE i = Pi.single i (a i) := by
  funext j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, h]

theorem letE_mul_self (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  rw [mul_letE]; simp [letE]

theorem mem_Nl_iff (i : ZMod n) (x : W.DD T) :
    x ∈ W.Nl T i ↔ x ∈ W.N T ∧ (letE i : LetA O n) • x = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(W.N T).smul_mem _ hy, ?_⟩
    change (letE i : LetA O n) • ((letE i : LetA O n) • y) = (letE i : LetA O n) • y
    rw [smul_smul, letE_mul_self]
  · rintro ⟨hx, he⟩
    exact ⟨x, hx, he⟩

theorem letE_smul_mem (i : ZMod n) {x : W.DD T} (hx : x ∈ W.N T) :
    (letE i : LetA O n) • x ∈ W.Nl T i := ⟨x, hx, rfl⟩

theorem φD_smulA (a : LetA O n) (x : W.DD T) : W.φD T (a • x) = W.φA a • W.φD T x := by
  have := W.φD_smul T (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.φE_ext, algebraMap_smul] at this
  exact this


include W in
theorem neZero_letters : NeZero n := by
  have := PD.finK₀
  exact ⟨by rw [W.n_eq]; exact Module.finrank_pos.ne'⟩

theorem isUnit_Q : IsUnit (algebraMap (LetA O n) W.EE W.Q) := by
  have hq : IsUnit (algebraMap (LetA O n) W.EE W.q) := by
    have h1 : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1 := by
      funext i
      simpa [letπ, LocWach.q] using W.q₀_def
    set x := algebraMap (LetA O n) W.EE letπ with hx
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq PD.hp (1 : W.EE) x
    obtain ⟨u, hu⟩ : IsUnit (x ^ PD.p) := W.EE_π.pow _
    have := W.EE_complete
    have hj : ((PD.p : ℕ) : W.EE) ∈ Ideal.jacobson (⊥ : Ideal W.EE) :=
      IsAdicComplete.le_jacobson_bot (Ideal.span {((PD.p : ℕ) : W.EE)})
        (Ideal.mem_span_singleton_self _)
    have h2 := (Ideal.mem_jacobson_bot.1 hj) (x * r * (↑u⁻¹ : W.EE))
    have h3 : x * algebraMap (LetA O n) W.EE W.q =
        (((PD.p : ℕ) : W.EE) * (x * r * (↑u⁻¹ : W.EE)) + 1) * u := by
      rw [hx, ← map_mul, h1, map_sub, map_pow, map_add (f := _), map_one, ← hx, hr, ← hu]
      have := u.inv_mul
      linear_combination (-((PD.p : ℕ) : W.EE) * x * r) * this
    exact isUnit_of_mul_isUnit_right (h3 ▸ h2.mul u.isUnit)
  have key : ∀ k : ℕ, IsUnit (algebraMap (LetA O n) W.EE ((W.φA ^ k) W.q)) := by
    intro k
    induction k with
    | zero => simpa using hq
    | succ k ih =>
      rw [pow_succ', AlgHom.mul_apply]
      have := W.φE_ext ((W.φA ^ k) W.q)
      exact this ▸ ih.map W.φE
  exact key _

theorem Q_pow_smul_cancel (m : ℕ) {x y : W.DD T} (h : W.Q ^ m • x = W.Q ^ m • y) : x = y := by
  rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE (W.Q ^ m) y, map_pow] at h
  exact ((isUnit_Q W).pow m).smul_left_cancel.1 h

variable {W T}

variable (W T)

end Generic

end GlobalTheory.WachLettersCompare
