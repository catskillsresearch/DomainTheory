/-ai
If a consistent finite set of tree tokens has nonempty atom projection, that atom projection is consistent in the atom information system.

Case on the consistency constructor. A left-consistent set supplies the atom consistency directly. A right-consistent set has empty atom projection, contradicting the nonempty hypothesis.
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

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys


variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem TreeCon_atom_con_of_atoms {u : Finset (TreeToken α)}
    (hu : TreeCon A u) (hne : atomFinset u ≠ ∅) : atomFinset u ∈ A.Con := by
  cases hu with
  | left _ hA _ _ => exact hA
  | right _ hA _ _ => exact False.elim (hne hA)

end InfoSys

end DomainTheory.InformationSystems
