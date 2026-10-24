module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826.Uapply
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826.Ulam
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826.translateAbs

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap


universe u

variable {α : Type u} {E : NeighborhoodSystem α}


/-- **A sanity check: the identity abstraction translates to the identity, and the recipe applied
to `body = id` (the trivial "translation" of a bare variable `σ = x`) already has the right type
for free** — `translateAbs a b (idMap E) = b∘a`, matching that a bare variable of type `D_a` fed
through the `a`-then-`b` sandwich needs no further work. Included as a `0`-th case of the
induction discussed above (the base case: variables). -/
theorem translateAbs_idMap {a b : ApproximableMap E E} : translateAbs a b (idMap E) = b.comp a := by
  unfold translateAbs
  rw [idMap_comp]

end DomainTheory.NeighbourhoodSystems
