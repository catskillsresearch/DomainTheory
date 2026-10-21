/-ai
A finite set of V-tokens entails each of its members.

Induct on the member. Bottom is entailed outright, and a member equal to top is entailed by the membership clause. A left-pair member projects to a member of the left pair projection, which the inductive hypothesis entails, and the left-projection clause lifts that entailment. A right-pair member is treated symmetrically.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.mem_vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.mem_vPairRFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

theorem VEnt_of_mem {u : Finset VToken} {c : VToken}
    (hc : c ∈ u) : VEnt u c := by
  induction c generalizing u with
  | bot => exact VEnt.bot
  | top => exact VEnt.top_mem hc
  | pairL x ih =>
    exact VEnt.pairL_proj (ih (mem_vPairLFinset.2 hc))
  | pairR y ih =>
    exact VEnt.pairR_proj (ih (mem_vPairRFinset.2 hc))

end InfoSys

end DomainTheory.InformationSystems
