/-ai
The supremum of the finite basis suprema of a sequence d over a set x of indices equals the supremum of the image of x under d.

The two sides are compared by antisymmetry. A finite basis supremum is the supremum of d on a finite subset t of x, and each value of d on t lies below the supremum of d on x by monotonicity of the image. Conversely, each value d n for n in x lies below the supremum of d on the singleton of n, and that singleton supremum is one of the finite basis suprema.
ai-/
module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Data.Finset.Basic
public import DomainTheory.DataTypesAsLattices.FixedLattices.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem sSup_finiteBasisSups {α : Type u} [CompleteLattice α]
    (d : ℕ → α) (x : Set ℕ) :
    sSup (finiteBasisSups d x) = sSup (d '' x) := by
  apply le_antisymm
  · apply sSup_le
    rintro y ⟨t, htx, rfl⟩
    apply sSup_le
    intro q hq
    exact le_sSup (Set.image_mono htx hq)
  · apply sSup_le
    rintro _ ⟨n, hn, rfl⟩
    calc
      d n ≤ sSup (d '' (({n} : Finset ℕ) : Set ℕ)) :=
        le_sSup ⟨n, by simp, rfl⟩
      _ ≤ sSup (finiteBasisSups d x) :=
        le_sSup ⟨{n}, by simpa, rfl⟩

end DomainTheory.DataTypesAsLattices
