/-ai
Tree entailment is transitive. If two finite sets of tree tokens are consistent, every token of the intermediate set is entailed by the stronger set, and the intermediate set entails a token, then the stronger set entails that token.

The consistency component is the consistency of the stronger set, and the payload component is transitivity of the entailment payload applied to the payload of the given entailment.
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
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeEntPayload_trans

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem TreeEnt_trans {u v : Finset (TreeToken α)} {c : TreeToken α}
    (hv : TreeCon A v) (hu : TreeCon A u)
    (hEnts : ∀ y ∈ u, TreeEnt A v y) (hEntc : TreeEnt A u c) :
    TreeEnt A v c :=
  ⟨hv, TreeEntPayload_trans A hv hu hEnts hEntc.2⟩

end InfoSys

end DomainTheory.InformationSystems
