module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst27
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamWF
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst70
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst74
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.listToLamDFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem mem_listToLamDFinset {xs : List (RawLamToken α)}
    {h : ∀ t ∈ xs, LamWF A t} {p : LamDToken A} :
    p ∈ listToLamDFinset A xs h ↔ p.val ∈ xs := by
  induction xs with
  | nil =>
    constructor
    · intro hp; exact False.elim (Finset.notMem_empty _ hp)
    · intro hp; cases hp
  | cons t ts ih =>
    constructor
    · intro hp
      rcases Finset.mem_insert.mp hp with hp | hp
      · subst hp; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih.1 hp)
    · intro hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (ih.2 hp)

end InfoSys

end DomainTheory.InformationSystems
