module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.mem_mapToOpen_openToMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.openToMap_mapToOpen

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise215

set_option linter.unusedVariables false

theorem example_215.{u_1} : And
  (∀ {γ : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ)
    (U : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V))
    (hU :
      @IsOpen (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement γ V) U)
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V),
    Iff
      (@Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V)
        (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V))
        (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V))
        (@DomainTheory.NeighbourhoodSystems.Exercise215.mapToOpen γ V
          (@DomainTheory.NeighbourhoodSystems.Exercise215.openToMap γ V U hU))
        x)
      (@Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V)
        (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V))
        (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V)) U x))
  (∀ {γ : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ)
    (f :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap γ
        (Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) V
        DomainTheory.NeighbourhoodSystems.Exercise215.O),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ
        (Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) V
        DomainTheory.NeighbourhoodSystems.Exercise215.O)
      (@DomainTheory.NeighbourhoodSystems.Exercise215.openToMap γ V
        (@DomainTheory.NeighbourhoodSystems.Exercise215.mapToOpen γ V f)
        (@DomainTheory.NeighbourhoodSystems.Exercise215.isOpen_mapToOpen γ V f))
      f) :=
  @And.intro
  (∀ {γ : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ)
    (U : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V))
    (hU :
      @IsOpen (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement γ V) U)
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V),
    Iff
      (@Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V)
        (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V))
        (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V))
        (@DomainTheory.NeighbourhoodSystems.Exercise215.mapToOpen γ V
          (@DomainTheory.NeighbourhoodSystems.Exercise215.openToMap γ V U hU))
        x)
      (@Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V)
        (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V))
        (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V)) U x))
  (∀ {γ : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ)
    (f :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap γ
        (Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) V
        DomainTheory.NeighbourhoodSystems.Exercise215.O),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ
        (Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) V
        DomainTheory.NeighbourhoodSystems.Exercise215.O)
      (@DomainTheory.NeighbourhoodSystems.Exercise215.openToMap γ V
        (@DomainTheory.NeighbourhoodSystems.Exercise215.mapToOpen γ V f)
        (@DomainTheory.NeighbourhoodSystems.Exercise215.isOpen_mapToOpen γ V f))
      f)
  @DomainTheory.NeighbourhoodSystems.Exercise215.mem_mapToOpen_openToMap
  @DomainTheory.NeighbourhoodSystems.Exercise215.openToMap_mapToOpen

end DomainTheory.NeighbourhoodSystems.Exercise215
