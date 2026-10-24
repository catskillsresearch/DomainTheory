module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeEntPayload

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]
variable (A : InfoSys α)

/-- Entailment for trees. -/
def TreeEnt (u : Finset (TreeToken α)) (p : TreeToken α) : Prop :=
  TreeCon A u ∧ TreeEntPayload A u p

theorem TreeEnt.of_mem {u : Finset (TreeToken α)} {p : TreeToken α}
    (hu : TreeCon A u) (hp : p ∈ u) : TreeEnt A u p :=
  ⟨hu, TreeEntPayload.of_mem A hu hp⟩

end InfoSys


end DomainTheory.InformationSystems
