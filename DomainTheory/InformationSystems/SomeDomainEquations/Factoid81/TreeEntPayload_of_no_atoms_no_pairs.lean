module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
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

theorem TreeEntPayload_of_no_atoms_no_pairs {u : Finset (TreeToken α)} {t : TreeToken α}
    (hAt : atomFinset u = ∅) (hL : pairLFinset u = ∅) (hR : pairRFinset u = ∅)
    (h : TreeEntPayload A u t) : t = .bot := by
  cases t with
  | bot => rfl
  | atom x => exact False.elim (h.1 hAt)
  | pairL t =>
    rcases h with ⟨_, _, _, hOr⟩
    rcases hOr with ⟨hne, _⟩ | ⟨_, hRne⟩
    · exact False.elim (hne hL)
    · exact False.elim (hRne hR)
  | pairR t =>
    rcases h with ⟨_, _, _, hOr⟩
    rcases hOr with ⟨hne, _⟩ | ⟨_, hLne⟩
    · exact False.elim (hne hR)
    · exact False.elim (hLne hL)

end InfoSys

end DomainTheory.InformationSystems
