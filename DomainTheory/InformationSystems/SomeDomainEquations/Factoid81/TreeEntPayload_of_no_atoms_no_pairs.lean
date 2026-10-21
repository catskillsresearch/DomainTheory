/-ai
If a finite set of tree tokens has empty atom projection and empty left and right pair projections, the only token in its entailment payload is the bottom.

Case on the token. The bottom case is reflexivity. An atom in the payload would require a nonempty atom projection. A left-pair token in the payload requires a nonempty left pair projection or a nonempty right pair projection. A right-pair token requires a nonempty right pair projection or a nonempty left pair projection.
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
