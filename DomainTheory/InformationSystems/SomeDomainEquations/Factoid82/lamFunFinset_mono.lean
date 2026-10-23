module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

theorem lamFunFinset_mono {u v : Finset (RawLamToken α)} (h : v ⊆ u) :
    lamFunFinset v ⊆ lamFunFinset u :=
  fun _ hp => mem_lamFunFinset.2 (h (mem_lamFunFinset.1 hp))

end InfoSys

end DomainTheory.InformationSystems
