/-ai
The atom projection of the singleton consisting of an atom token is the singleton of that atom.

Membership in the projection is membership of the atom token in the singleton. The atom constructor is injective, and an equality of atoms is preserved by the atom constructor.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.mem_atomFinset

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u

variable {α : Type*} [DecidableEq α]

theorem atomFinset_singleton_atom (x : α) :
    atomFinset ({.atom x} : Finset (TreeToken α)) = {x} := by
  ext y; simp only [mem_atomFinset, Finset.mem_singleton]
  exact ⟨fun h => TreeToken.atom.inj h, fun h => congrArg TreeToken.atom h⟩

end InfoSys

end DomainTheory.InformationSystems
