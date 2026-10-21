/-ai
An atom belongs to the atom projection of a finite set of tree tokens if and only if the corresponding atom token belongs to the set.

The membership lemma for the fold of atom insertion supplies a token of the underlying multiset equal to the atom token, which is membership in the finite set. Conversely, the atom token itself is such a witness.
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
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.mem_foldr_atom

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys


variable {α : Type*} [DecidableEq α]

theorem mem_atomFinset {u : Finset (TreeToken α)} {x : α} :
    x ∈ atomFinset u ↔ .atom x ∈ u := by
  constructor
  · intro hx
    rcases (mem_foldr_atom u.1 x).1 hx with ⟨p, hp, hp'⟩
    subst hp'; exact Finset.mem_def.2 hp
  · intro hx
    exact (mem_foldr_atom u.1 x).2 ⟨.atom x, Finset.mem_def.1 hx, rfl⟩

end InfoSys

end DomainTheory.InformationSystems
