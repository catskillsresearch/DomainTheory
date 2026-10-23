module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeToken
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

omit [DecidableEq α] in

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
