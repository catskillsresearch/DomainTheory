module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.isProjection_piU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.isFinitary_piU_of_isFinitary_piD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.isFinitaryProjection_piD

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap


/-- **Exercise 8.27, in full: for `d` a polymorphic type, `Π(d)` is a type.** (In fact for *any*
`d` at all — see `isFinitaryProjection_piD`.) This is the exercise's own statement, the last exercise
in the book, closed. -/
theorem isFinitaryProjection_piU (d : ApproximableMap U U) : FinitaryProjection (piU d) :=
  ⟨⟨isProjection_piU d, isFinitary_piU_of_isFinitary_piD (isFinitaryProjection_piD d).out.2⟩⟩

end DomainTheory.NeighbourhoodSystems
