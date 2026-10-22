/-ai
An element of an information system is a set of tokens such that every finite subset is consistent and the set is closed under entailment.
ai-/
module


public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Basic
public import DomainTheory.InformationSystems.InformationSystems.InfoSys.InfoSys

@[expose] public section

universe u

namespace DomainTheory.InformationSystems
namespace InfoSys

variable {α : Type u} [DecidableEq α] (sys : InfoSys α)

/-- An *element* (ideal) of the domain: a set of tokens that is consistent on every
finite subset and closed under entailment. -/
structure Element where
  /-- The underlying set of tokens. -/
  carrier : Set α
  /-- Every finite subset of the element is consistent. -/
  consistent : ∀ Y : Finset α, (Y : Set α) ⊆ carrier → Y ∈ sys.Con
  /-- The element is closed under entailment. -/
  closed : ∀ (Y : Finset α) (a : α), (Y : Set α) ⊆ carrier → sys.Ent Y a → a ∈ carrier

end InfoSys
end DomainTheory.InformationSystems
