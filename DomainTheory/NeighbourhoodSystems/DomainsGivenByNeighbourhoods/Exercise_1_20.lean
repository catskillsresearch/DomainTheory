module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NeighborhoodSystem_more

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem
variable {α : Type*} (V : NeighborhoodSystem α)

/-- Scott's Exercise 1.20: a system is isomorphic to its power system; the power system
    is positive; principals map to principals. -/
theorem exercise_1_20 :
    (V ≅ᴰ V.powerSystem) ∧
      V.powerSystem.IsPositive ∧
        ∀ {X : Set α} (hX : V.mem X),
          V.toPower (V.principal hX) = V.powerSystem.principal ⟨X, hX, rfl⟩ :=
  ⟨V.isomorphic_powerSystem, V.powerSystem_isPositive, V.toPower_principal⟩

