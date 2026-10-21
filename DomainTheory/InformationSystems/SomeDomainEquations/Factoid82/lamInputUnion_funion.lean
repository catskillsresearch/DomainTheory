/-ai
The input union of a choice-free union of finite sets of raw-token list pairs equals the choice-free union of the two input unions.

Extensionality splits each direction by the membership criteria for input union and for choice-free union. A token in the input union of the union comes from the first list of a pair lying on one side or the other, so it lies in that side's input union. A token in either input union comes from a pair on that side, and that pair still belongs to the choice-free union.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst27

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem lamInputUnion_funion
    (s t : Finset (List (RawLamToken α) × List (RawLamToken α))) :
    lamInputUnion (s ∪' t) = lamInputUnion s ∪' lamInputUnion t := by
  ext x
  constructor
  · intro hx
    rcases (mem_lamInputUnion).1 hx with ⟨p, hp, hx'⟩
    rcases mem_funion.1 hp with hp | hp
    · exact mem_funion.2 (Or.inl ((mem_lamInputUnion).2 ⟨p, hp, hx'⟩))
    · exact mem_funion.2 (Or.inr ((mem_lamInputUnion).2 ⟨p, hp, hx'⟩))
  · intro hx
    rcases mem_funion.1 hx with hx | hx
    · rcases (mem_lamInputUnion).1 hx with ⟨p, hp, hx'⟩
      exact (mem_lamInputUnion).2 ⟨p, mem_funion.2 (Or.inl hp), hx'⟩
    · rcases (mem_lamInputUnion).1 hx with ⟨p, hp, hx'⟩
      exact (mem_lamInputUnion).2 ⟨p, mem_funion.2 (Or.inr hp), hx'⟩

end InfoSys

end DomainTheory.InformationSystems
