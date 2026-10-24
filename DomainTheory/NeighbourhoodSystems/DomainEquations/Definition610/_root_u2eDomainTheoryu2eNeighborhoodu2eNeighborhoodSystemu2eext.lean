module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610.Subsystem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610.Basic.notation2

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

variable {α : Type*}


namespace Subsystem

/-- Two neighbourhood systems with the same `mem` and the same `master` are equal (the remaining
fields of `NeighborhoodSystem` are `Prop`s). -/
theorem _root_.DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.ext {D E : NeighborhoodSystem α}
    (hmem : ∀ X, D.mem X ↔ E.mem X) (hmaster : D.master = E.master) : D = E := by
  rcases D with ⟨Dmem, Dmaster, _, _, _⟩
  rcases E with ⟨Emem, Emaster, _, _, _⟩
  have hm : Dmem = Emem := funext fun X => propext (hmem X)
  subst hm
  subst hmaster
  rfl

end Subsystem
end DomainTheory.NeighbourhoodSystems
