/-ai
The output union of a finite set of raw-token list pairs with one pair inserted equals the finite set of the inserted pair's second list, joined by choice-free union to the output union of the original set.

A token in the enlarged output union comes from some pair in the insertion. If that pair is the inserted one, the token lies in its second list; otherwise it lies in the original output union. Conversely, a token from the inserted second list comes from the inserted pair, and a token from the original output union comes from a pair that remains a member after insertion.
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

theorem lamOutputUnion_insert
    (s : Finset (List (RawLamToken α) × List (RawLamToken α)))
    (p : List (RawLamToken α) × List (RawLamToken α)) :
    lamOutputUnion (insert p s) = listToFinset p.2 ∪' lamOutputUnion s := by
  ext t
  constructor
  · intro ht
    rcases (mem_lamOutputUnion).1 ht with ⟨q, hq, ht'⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact mem_funion.2 (Or.inl ht')
    · exact mem_funion.2 (Or.inr ((mem_lamOutputUnion).2 ⟨q, hq, ht'⟩))
  · intro ht
    rcases mem_funion.1 ht with ht | ht
    · exact (mem_lamOutputUnion).2 ⟨p, Finset.mem_insert_self p s, ht⟩
    · rcases (mem_lamOutputUnion).1 ht with ⟨q, hq, ht'⟩
      exact (mem_lamOutputUnion).2 ⟨q, Finset.mem_insert_of_mem hq, ht'⟩

end InfoSys

end DomainTheory.InformationSystems
