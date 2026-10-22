/-ai
A map on the power set of the natural numbers is approximable when it preserves inclusion and every output is already produced by the set of entries of some finite list drawn from the input. Preservation of inclusion is stated directly, so that the predicate does not pass through the choice-dependent lattice order on sets.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise513
public import Mathlib.Data.List.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.tag_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.tag_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.entries
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.mem_entries

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise514

open DomainTheory.NeighbourhoodSystems.Exercise513

/-- A map `f : Pω → Pω` is *approximable* (continuous) when it is monotone and every output is
already produced by a finite subset of the input. The finite subsets of `x` are exactly the
`entries ns` with all entries in `x`.

Monotonicity is phrased as an explicit `⊆`-implication rather than `Monotone f`: on `Set ℕ` the
order `≤` resolves through the `CompleteLattice` instance whose construction uses `Classical.choice`,
so the `Monotone`-based statement would not be choice-free. The two are definitionally equal. -/
def IsApprox (f : Set ℕ → Set ℕ) : Prop :=
  (∀ ⦃x x' : Set ℕ⦄, x ⊆ x' → f x ⊆ f x') ∧
    ∀ x m, m ∈ f x → ∃ ns, (∀ n ∈ ns, n ∈ x) ∧ m ∈ f (entries ns)

end DomainTheory.NeighbourhoodSystems.Exercise514
