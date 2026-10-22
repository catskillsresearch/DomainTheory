/-ai
Insertion into the finset of function-token pairs is left commutative. Comparing the two orders cases on both raw tokens and uses commutativity of finset insertion, or reflexivity when the two sides agree.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamFunInsert
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst9

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

instance : LeftCommutative
    (lamFunInsert : RawLamToken α →
      Finset (List (RawLamToken α) × List (RawLamToken α)) →
        Finset (List (RawLamToken α) × List (RawLamToken α))) :=
  ⟨fun p q s => by cases p <;> cases q <;> first | exact insert_comm' _ _ s | rfl⟩

end InfoSys

end DomainTheory.InformationSystems
