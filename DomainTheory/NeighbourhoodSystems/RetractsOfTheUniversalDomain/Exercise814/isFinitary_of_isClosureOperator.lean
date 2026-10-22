module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}


section FiniteDomain

variable {a : ApproximableMap E E} (h : ClosureOperator a)


/-- **Exercise 8.14 (Scott 1981, PRG-19), the main theorem.** For any closure operator
`a : E → E`, the fixed-point set of `a` is a finitary domain. -/
theorem isFinitary_of_isClosureOperator (h : ClosureOperator a) : IsFinitary a :=
  ⟨CompactFix h, domainOfClosure h, ⟨fixSetOrderIso h⟩⟩

end FiniteDomain
end DomainTheory.NeighbourhoodSystems
