module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.functionSystem
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

theorem lamInputUnion_funion
    (s t : Finset (List (RawLamToken α) × List (RawLamToken α))) :
    lamInputUnion (s ∪' t) = lamInputUnion s ∪' lamInputUnion t := by
  ext x
  constructor
  · intro hx
    rcases (mem_lamInputUnion).1 hx with ⟨p, hp, hx'⟩
    rcases funion.mem.1 hp with hp | hp
    · exact funion.mem.2 (Or.inl ((mem_lamInputUnion).2 ⟨p, hp, hx'⟩))
    · exact funion.mem.2 (Or.inr ((mem_lamInputUnion).2 ⟨p, hp, hx'⟩))
  · intro hx
    rcases funion.mem.1 hx with hx | hx
    · rcases (mem_lamInputUnion).1 hx with ⟨p, hp, hx'⟩
      exact (mem_lamInputUnion).2 ⟨p, funion.mem.2 (Or.inl hp), hx'⟩
    · rcases (mem_lamInputUnion).1 hx with ⟨p, hp, hx'⟩
      exact (mem_lamInputUnion).2 ⟨p, funion.mem.2 (Or.inr hp), hx'⟩

end InfoSys

end DomainTheory.InformationSystems
