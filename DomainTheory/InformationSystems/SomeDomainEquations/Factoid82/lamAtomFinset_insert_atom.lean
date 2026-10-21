/-ai
Inserting an atom token into a finite set of raw lambda tokens inserts that atom into the atom set.

By extensionality and the membership rule for the atom set, membership splits into the inserted token or membership in the original set. The inserted token is the given atom by injectivity of the atom constructor, and the two directions match these cases.
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
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.mem_lamAtomFinset

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

theorem lamAtomFinset_insert_atom (u : Finset (RawLamToken α)) (x : α) :
    lamAtomFinset (insert (.atom x) u) = insert x (lamAtomFinset u) := by
  ext y; simp only [Finset.mem_insert, mem_lamAtomFinset]
  constructor
  · rintro (h | h)
    · exact Or.inl (RawLamToken.atom.inj h)
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h

end InfoSys

end DomainTheory.InformationSystems
