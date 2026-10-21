/-ai
A nonempty finite set of tree tokens contained in the singleton of the bottom equals that singleton.

By extensionality, every member of the set lies in the singleton. Conversely the only candidate element is the bottom. Nonemptiness supplies some element of the set, the inclusion forces that element to be the bottom, and therefore the bottom belongs to the set.
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

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem eq_singleton_bot_of_subset {s : Finset (TreeToken α)}
    (hne : s ≠ ∅) (hsub : s ⊆ {.bot}) : s = {.bot} := by
  ext y
  constructor
  · exact fun hy => hsub hy
  · intro hy
    have : y = .bot := Finset.mem_singleton.1 hy
    subst this
    obtain ⟨z, hz⟩ := Finset.nonempty_of_ne_empty hne
    have hzbot : z = .bot := Finset.mem_singleton.1 (hsub hz)
    exact hzbot ▸ hz

end InfoSys

end DomainTheory.InformationSystems
