module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

@[expose] public section

open NumberField

namespace PositivityTheory.Pf1.CLGD.K

namespace LKW

theorem not_real_complex (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)

end LKW

end PositivityTheory.Pf1.CLGD.K
