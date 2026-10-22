/-ai
The atom set grows along inclusion of finite sets of raw lambda tokens.

An atom of the smaller set is an atom token of that set, hence of the larger set, and therefore an atom of the larger atom set.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.mem_lamAtomFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

theorem lamAtomFinset_mono {u v : Finset (RawLamToken α)} (h : v ⊆ u) :
    lamAtomFinset v ⊆ lamAtomFinset u :=
  fun _ hx => mem_lamAtomFinset.2 (h (mem_lamAtomFinset.1 hx))

end InfoSys

end DomainTheory.InformationSystems
