/-ai
An element is compact when, whenever it lies below a directed supremum indexed in the neighbourhood system's own universe, it already lies below some summand. By algebraicity this is the same as being principal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.fixedNbhd_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.BasicInst8

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section Algebraic

variable {γ : Type u} {V : NeighborhoodSystem γ}

/-- **Compactness, as a standalone predicate**: `x` is compact iff every time `x` sits below a
directed union it already sits below one of the summands. By algebraicity, this is exactly the
same thing as being principal (`eq_principal_of_isCompactElt`). Stated with `I` fixed to `V`'s own
token universe (the only instantiation ever needed below), to sidestep spurious universe-metavariable
friction from a separately-auto-bound `Type*` inside a reusable `def`. -/
def IsCompactElt (x : V.Element) : Prop :=
  ∀ {I : Type u} [Nonempty I] (d : I → V.Element) (hdir : ∀ i j, ∃ k, d i ≤ d k ∧ d j ≤ d k),
    x ≤ iSupDirected d hdir → ∃ i, x ≤ d i

end Algebraic

end DomainTheory.NeighbourhoodSystems
