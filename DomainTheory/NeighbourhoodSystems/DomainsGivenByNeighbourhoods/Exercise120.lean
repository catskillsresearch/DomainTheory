module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.isomorphic_powerSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.powerSystem_isPositive
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.toPower_principal

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem

set_option linter.unusedVariables false

theorem example_120.{u_1} : And
  (And
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.Isomorphic α (Set α) V
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive (Set α)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X : Set α}
    (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Set α)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V))
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.toPower α V
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V X hX))
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal (Set α)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X)
        (@Exists.intro (Set α)
          (fun (X_1 : Set α) =>
            And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X_1)
              (@Eq (Set (Set α)) (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X_1)))
          X
          (@And.intro (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X)
            (@Eq (Set (Set α)) (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X))
            hX (@rfl (Set (Set α)) (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X)))))) :=
  @And.intro
  (And
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.Isomorphic α (Set α) V
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive (Set α)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X : Set α}
    (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Set α)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V))
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.toPower α V
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V X hX))
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal (Set α)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X)
        (@Exists.intro (Set α)
          (fun (X_1 : Set α) =>
            And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X_1)
              (@Eq (Set (Set α)) (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X_1)))
          X
          (@And.intro (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X)
            (@Eq (Set (Set α)) (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X))
            hX (@rfl (Set (Set α)) (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X))))))
  (@And.intro
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.Isomorphic α (Set α) V
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive (Set α)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V))
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.isomorphic_powerSystem
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem_isPositive)
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.toPower_principal

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
