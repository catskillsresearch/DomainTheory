module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.isFinitaryProjection_piD_of_formula
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.hii_piD

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap






















































/-- **Exercise 8.27(b)(4): `piD d` is a finitary projection, for every `d`** (Exercise 8.27(b)(1)
specialized to `hii_piD`). Combined with Exercise 8.27(b)(0) (`isFinitary_piU_of_isFinitary_piD`),
this closes "`Π(d)` is a type" — Scott's own hint, in full, and *without even needing `d` to be a
polymorphic type* (a strictly stronger statement than the exercise asks for). -/
theorem isFinitaryProjection_piD (d : ApproximableMap U U) : IsFinitaryProjection (piD d) :=
  isFinitaryProjection_piD_of_formula d (fun x => hii_piD d x)

end DomainTheory.NeighbourhoodSystems
