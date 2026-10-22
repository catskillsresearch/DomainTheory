module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub_sub
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.isFinitaryProjection_of_sub_eq_self

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}


/-- **`sub` is itself a finitary projection on `E → E`'s range** (Theorem 8.6's remark that `sub`
restricted to its own range is the identity, i.e. `sub` "is" a projection onto the finitary
projections): applying `sub` twice is the same as once (`sub_sub`), and every `sub f` is already a
fixed point of `sub` (feed `isFinitaryProjection_of_sub_eq_self (sub_sub f)` back through
`sub_eq_self_iff_isFinitaryProjection`) — i.e. `sub f` is *always* a finitary projection, for any
`f`, needing no hypothesis on `f` at all. -/
theorem isFinitaryProjection_sub (f : ApproximableMap E E) : FinitaryProjection (sub f) :=
  isFinitaryProjection_of_sub_eq_self (sub_sub f)

end DomainTheory.NeighbourhoodSystems
