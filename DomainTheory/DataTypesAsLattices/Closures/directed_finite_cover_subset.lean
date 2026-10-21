/-ai
If a family of fixed points is a directed subset, and a finite set is contained in the union of their underlying sets, then some member of the family contains that finite set.

A directed subset is a directed set by copying its pairwise upper bounds. The finite-cover lemma for directed sets of values, transported along the underlying-set coercion, gives the member.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


















theorem directed_finite_cover_subset {f : Pomega → Pomega}
    {A : Set (Fixpoints f)} (hA : IsDirectedSubset A) {t : Pomega}
    (ht : t.Finite) (hsub : t ⊆ ⋃₀ (Subtype.val '' A)) :
    ∃ z ∈ A, t ⊆ z := by
  have hA' : IsDirectedSet A := by
    refine ⟨hA.1, ?_⟩
    intro x hx y hy
    obtain ⟨z, hz, hxz, hyz⟩ := hA.2 hx hy
    exact ⟨z, hz, hxz, hyz⟩
  simpa [Fixpoints.vals] using directed_finite_cover hA' ht (by
    simpa [Fixpoints.vals] using hsub)

end DomainTheory.DataTypesAsLattices
