module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Definition22.EntSet

@[expose] public section

namespace DomainTheory.InformationSystems

namespace InfoSys

universe u

variable {α : Type u} [DecidableEq α] (sys : InfoSys α)

theorem entSet_singleton {u : Finset α} {X : α} :
    sys.EntSet u {X} ↔ sys.Ent u X := by
  constructor
  · intro h
    exact h X (Finset.mem_singleton_self X)
  · intro h Y hY
    rw [Finset.mem_singleton] at hY
    subst hY
    exact h

end InfoSys
end DomainTheory.InformationSystems
