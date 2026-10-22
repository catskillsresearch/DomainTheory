module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.isRetraction_a

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂


variable {α : Type*} {D : NeighborhoodSystem α}


variable (u : D.Element) (hu : u ≠ D.bot)


/-- **Example 8.4(a) (Scott 1981, PRG-19), final statement.** If `D` is not trivial (`u ≠ ⊥`),
`a(x) = fade(check(x), u)` is a retraction on `D` whose range is isomorphic to `O = {{0},{0,1}}`. -/
theorem example84a (hu : u ≠ D.bot) :
    Retraction (a u) ∧ Nonempty (O.Element ≃o {y : D.Element // (a u).toElementMap y = y}) :=
  ⟨isRetraction_a u hu, ⟨fixIso u hu⟩⟩
end DomainTheory.NeighbourhoodSystems
