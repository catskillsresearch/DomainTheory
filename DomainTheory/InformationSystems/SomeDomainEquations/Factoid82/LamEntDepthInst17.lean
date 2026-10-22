/-ai
Insertion into an input union is left commutative, assuming decidable equality of raw tokens. After unfolding the operation, membership in the union is a three-way disjunction, and the two orders match by rearranging those disjuncts.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst9
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst10
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamInUnionInsert

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

instance [DecidableEq (RawLamToken α)] :
    LeftCommutative (lamInUnionInsert (α := α)) :=
  ⟨fun p q s => by
    simp only [lamInUnionInsert]
    ext x; simp only [mem_funion]
    constructor <;> · rintro (h | h | h); exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h)]⟩

end InfoSys

end DomainTheory.InformationSystems
