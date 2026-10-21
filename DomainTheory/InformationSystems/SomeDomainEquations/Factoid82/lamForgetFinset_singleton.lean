/-ai
Forgetting a singleton lambda token yields the singleton of its underlying raw token.

By extensionality, a raw token in the forget comes from the unique member of the singleton, which is the given token. Conversely the given token is that unique member, and forgetting it returns the raw token of the singleton.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.mem_lamForgetFinset

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)












theorem lamForgetFinset_singleton (p : LamToken A) :
    lamForgetFinset A {p} = {p.val} := by
  ext t
  constructor
  · intro ht
    rcases (mem_lamForgetFinset A).1 ht with ⟨q, hq, hq'⟩
    have : q = p := Finset.mem_singleton.mp hq
    subst this; exact Finset.mem_singleton.mpr hq'.symm
  · intro ht
    exact (mem_lamForgetFinset A).2
      ⟨p, Finset.mem_singleton_self p, (Finset.mem_singleton.mp ht).symm⟩

end InfoSys
end DomainTheory.InformationSystems
