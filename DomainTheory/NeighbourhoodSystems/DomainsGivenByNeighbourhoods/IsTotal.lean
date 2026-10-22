module

public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NeighborhoodSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Element
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.interUpTo_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.interUpTo_succ
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.BasicInst22
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.mem_principal
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.mem_bot
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.BasicInst34

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Definition 1.8 (Scott 1981, PRG-19) — *total* elements.** "Elements maximal with respect
to the approximation relation are called *total elements*." `x` is total iff it is maximal: any
`y` it approximates approximates it back. This is the *predicate* only; the *existence* of total
elements above a given `x` (Exercise 1.24) is choice-dependent and out of scope here. -/
def IsTotal (x : V.Element) : Prop := ∀ y, x ≤ y → y ≤ x

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
