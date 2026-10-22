module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419


variable {β : Type*}

/-- Two approximable maps out of `C` agree as soon as they agree on every finite element `σ⊥` and
`σ` (Exercise 2.8). This is the workhorse for the map equalities below. -/
theorem map_ext_C {V : NeighborhoodSystem β} {f g : ApproximableMap C V}
    (hbot : ∀ σ, f.toElementMap (strBot σ) = g.toElementMap (strBot σ))
    (helem : ∀ σ, f.toElementMap (strElem σ) = g.toElementMap (strElem σ)) : f = g := by
  apply eq_of_toElementMap_principal
  intro X hX
  obtain (⟨σ, rfl⟩ | ⟨σ, rfl⟩) := (C_mem.mp hX)
  · exact hbot σ
  · exact helem σ

end DomainTheory.NeighbourhoodSystems.Exercise516
