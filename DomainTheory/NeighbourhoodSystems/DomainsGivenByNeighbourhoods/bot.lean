module

public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NeighborhoodSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Element
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.interUpTo_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.interUpTo_succ
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.BasicInst22
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.principal
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.mem_principal

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Definition 1.8 (Scott 1981, PRG-19) — `⊥`.** The least defined element `⊥ = {Δ}`,
"read: *bottom*". It is the principal filter of the master neighbourhood `Δ`: `⊥ = ↑Δ`. -/
def bot : V.Element := V.principal V.master_mem

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
