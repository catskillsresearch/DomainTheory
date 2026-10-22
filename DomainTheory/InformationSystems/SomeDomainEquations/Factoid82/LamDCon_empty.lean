/-ai
The empty finset of depth-well-formed lambda tokens is bundled-consistent.

Its forgetful image is empty, and the empty finset of raw tokens is depth-consistent.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamDForgetFinset_empty

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]


variable (A : InfoSys α)


theorem LamDCon_empty : LamDCon A (∅ : Finset (LamDToken A)) := by
  simpa [LamDCon, lamDForgetFinset_empty] using LamConDepth_empty A

end InfoSys
end DomainTheory.InformationSystems
