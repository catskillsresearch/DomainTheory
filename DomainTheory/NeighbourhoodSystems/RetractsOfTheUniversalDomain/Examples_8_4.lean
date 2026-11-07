module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.fixOfO
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.smashRetraction
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.strictRetraction
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.fixedNbhd

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

/-- Scott's Examples 8.4: check/fade give a retraction onto $O$; strict and smash
are projections onto the strict function space and smash product. -/
theorem example_84 :
    (∀ {α : Type*} {D : NeighborhoodSystem α} (u : D.Element),
      u ≠ D.bot →
        Retraction (a u) ∧
          Nonempty (O.Element ≃o {y : D.Element // (a u).toElementMap y = y})) ∧
    (∀ {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β},
      IsProjection (strictRetraction (D := D) (E := E)) ∧
        Nonempty ((SmashProduct.strictFun D E).Element ≃o
          {φ : (funSpace D E).Element // strictRetraction.toElementMap φ = φ})) ∧
    (∀ {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β},
      IsProjection (smashRetraction (D := D) (E := E)) ∧
        Nonempty ((SmashProduct.smash D E).Element ≃o
          {z : (prod D E).Element // smashRetraction.toElementMap z = z})) :=
  ⟨@example84a, ⟨@example84b_strict, @example84b_smash⟩⟩

end DomainTheory.NeighbourhoodSystems
