/-ai
A neighbourhood system D is a subsystem of a neighbourhood system E when the two systems have the same master neighbourhood, every neighbourhood of D is a neighbourhood of E, and the intersection of two neighbourhoods of D is a neighbourhood of D whenever it is a neighbourhood of E.
ai-/
module


public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

variable {α : Type*}

/-- **Definition 6.10 (Scott 1981, PRG-19).** The *subsystem* (subdomain) relation `D ◁ E` for two
neighbourhood systems over the same token type. It records that `D` and `E` are systems over the
same `Δ` (`master_eq`), that `D` is a subfamily of `E` (`sub`), and — the essential clause — that
consistency is inherited from `E`: an intersection of two `D`-neighbourhoods that happens to be an
`E`-neighbourhood is already a `D`-neighbourhood (`inter_closed`). -/
structure Subsystem (D E : NeighborhoodSystem α) : Prop where
  /-- `D` and `E` are systems over the same set of tokens `Δ`. -/
  master_eq : D.master = E.master
  /-- `D ⊆ E`: every neighbourhood of `D` is a neighbourhood of `E`. -/
  sub : ∀ {X : Set α}, D.mem X → E.mem X
  /-- Consistency in `D` is the same as in `E`: if `X, Y ∈ D` and `X ∩ Y ∈ E`, then `X ∩ Y ∈ D`. -/
  inter_closed : ∀ {X Y : Set α}, D.mem X → D.mem Y → E.mem (X ∩ Y) → D.mem (X ∩ Y)

end DomainTheory.NeighbourhoodSystems
