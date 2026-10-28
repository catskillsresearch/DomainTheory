module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Basic
public import DomainTheory.InformationSystems.InformationSystems.InfoSys.InfoSys

@[expose] public section

universe u

namespace DomainTheory.InformationSystems
namespace InfoSys

variable {α : Type u} [DecidableEq α] (sys : InfoSys α)

structure Element where

  carrier : Set α

  consistent : ∀ Y : Finset α, (Y : Set α) ⊆ carrier → Y ∈ sys.Con

  closed : ∀ (Y : Finset α) (a : α), (Y : Set α) ⊆ carrier → sys.Ent Y a → a ∈ carrier

end InfoSys
end DomainTheory.InformationSystems
