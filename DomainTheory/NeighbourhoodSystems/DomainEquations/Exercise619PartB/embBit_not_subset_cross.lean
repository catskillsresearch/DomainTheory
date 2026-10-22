module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.ScottSys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.FExpr

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}

/-- A non-empty `b`-tagged copy can never sit inside a `b'`-tagged copy for `b ≠ b'`. -/
theorem embBit_not_subset_cross {b b' : Bool} (h : b ≠ b') {X Y : Set Str} (hX : X.Nonempty)
    (hsub : embBit b X ⊆ embBit b' Y) : False := by
  obtain ⟨t, ht⟩ := hX
  obtain ⟨w', he, -⟩ := hsub ⟨t, rfl, ht⟩
  simp only [List.cons.injEq] at he
  exact h he.1

end Exercise619

end DomainTheory.NeighbourhoodSystems
