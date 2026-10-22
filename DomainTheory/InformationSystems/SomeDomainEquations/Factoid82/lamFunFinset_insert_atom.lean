/-ai
Inserting an atom token into a finite set of raw lambda tokens leaves the function set unchanged.

By extensionality and the membership rule for the function set, membership in the insertion is the inserted token or membership in the original set. The inserted atom is not a function token, so membership is membership in the original function set, and every original pair embeds into the insertion.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

theorem lamFunFinset_insert_atom (u : Finset (RawLamToken α)) (x : α) :
    lamFunFinset (insert (.atom x) u) = lamFunFinset u := by
  ext p; simp only [mem_lamFunFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

end InfoSys

end DomainTheory.InformationSystems
