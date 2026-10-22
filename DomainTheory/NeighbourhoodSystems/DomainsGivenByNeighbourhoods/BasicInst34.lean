/-ai
That partial order has a least element, the filter whose only neighbourhood is the master. This packages Scott's Factoid 1.8a.
ai-/
module

public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NeighborhoodSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Element
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.interUpTo_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.interUpTo_succ
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.BasicInst22
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.mem_principal
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.bot
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.mem_bot
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.bot_le

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Factoid 1.8a, packaged.** `⊥` is an `OrderBot` for the approximation order, so the `⊥`
notation refers to `{Δ}`. Constructive (`bot_le` is `[propext, Quot.sound]`). -/
instance : OrderBot V.Element where
  bot := V.bot
  bot_le := V.bot_le

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
