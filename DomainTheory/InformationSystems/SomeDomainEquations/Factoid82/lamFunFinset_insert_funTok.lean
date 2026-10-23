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

theorem lamFunFinset_insert_funTok (u : Finset (RawLamToken α))
    (xs ys : List (RawLamToken α)) :
    lamFunFinset (insert (.funTok xs ys) u) = insert (xs, ys) (lamFunFinset u) := by
  ext p; simp only [Finset.mem_insert, mem_lamFunFinset]
  constructor
  · rintro (h | h)
    · exact Or.inl (Prod.ext (RawLamToken.funTok.inj h).1 (RawLamToken.funTok.inj h).2)
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h

end InfoSys

end DomainTheory.InformationSystems
