/-ai
A raw token lies in the forget-finset of a finite set of lambda tokens if and only if some member has that raw value.

Simplifying the definition of the forget-finset reduces the equivalence to the membership lemma for the right fold of forget-insertion.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]


variable (A : InfoSys α)


theorem mem_lamForgetFinset {u : Finset (LamToken A)} {t : RawLamToken α} :
    t ∈ lamForgetFinset A u ↔ ∃ p ∈ u, p.val = t := by
  simpa [lamForgetFinset] using mem_foldr_lamForget A u.1 t

end InfoSys
end DomainTheory.InformationSystems
