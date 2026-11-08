module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys

@[expose] public section

namespace DomainTheory.InformationSystems

namespace InfoSys

universe u

variable {α : Type u} [DecidableEq α] (sys : InfoSys α)

def EntSet (u v : Finset α) : Prop := ∀ X ∈ v, sys.Ent u X

namespace EntSet

theorem empty (u : Finset α) : sys.EntSet u (∅ : Finset α) := by
  intro X hX
  exact False.elim (Finset.notMem_empty X hX)

theorem singleton {u : Finset α} {X : α} :
    sys.EntSet u {X} ↔ sys.Ent u X := by
  constructor
  · intro h
    exact h X (Finset.mem_singleton_self X)
  · intro h Y hY
    rw [Finset.mem_singleton] at hY
    subst hY
    exact h

end EntSet

end InfoSys

end DomainTheory.InformationSystems
