/-ai
A finite set u of sum tokens entails a sum token p, in the sense of Scott's Definition 6.3(iv') through (iv'''), when u is sum-consistent and the condition on p is trivial for the sum bottom, the left projection of u is nonempty and A entails the component from that projection for a left token, and the right projection of u is nonempty and B entails the component from that projection for a right token. Sum consistency is included so that the entailment-consistency law can update the projections.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instDecidableEqSumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeLftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeRhtInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumCon

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

/-- Entailment for the separated sum (Scott 6.3(iv')–(iv''')).
Includes `SumCon` so `ent_con` can update projections. -/
def SumEnt (u : Finset (SumToken α β)) (p : SumToken α β) : Prop :=
  SumCon A B u ∧
    match p with
    | .bot => True
    | .left x => lftFinset u ≠ ∅ ∧ A.Ent (lftFinset u) x
    | .right y => rhtFinset u ≠ ∅ ∧ B.Ent (rhtFinset u) y

end InfoSys

end DomainTheory.InformationSystems
