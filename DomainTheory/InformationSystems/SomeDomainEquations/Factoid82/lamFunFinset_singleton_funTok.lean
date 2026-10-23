module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst27

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem lamFunFinset_singleton_funTok (u v : List (RawLamToken α)) :
    lamFunFinset ({.funTok u v} : Finset (RawLamToken α)) = {(u, v)} := by
  ext p
  simp only [mem_lamFunFinset, Finset.mem_singleton]
  constructor
  · intro h
    exact Prod.ext (RawLamToken.funTok.inj h).1 (RawLamToken.funTok.inj h).2
  · intro h
    cases h
    rfl

end InfoSys

end DomainTheory.InformationSystems
