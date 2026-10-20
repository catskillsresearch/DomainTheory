module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.listToFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst9
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst10

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem mem_listToFinset {β : Type*} [DecidableEq β] {x : β} {xs : List β} :
    x ∈ listToFinset xs ↔ x ∈ xs := by
  induction xs with
  | nil =>
    constructor
    · intro h; exact False.elim (Finset.notMem_empty x h)
    · intro h; cases h
  | cons a as ih =>
    simp only [listToFinset, Finset.mem_insert, List.mem_cons, ih]

end InfoSys

end DomainTheory.InformationSystems
