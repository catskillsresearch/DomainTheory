module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Order.Directed
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ofC_toC

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))


variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)


variable (hne : C.Nonempty)


variable (hDir : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → DirectedOn (· ⊆ ·) 𝒮 → ⋃₀ 𝒮 ∈ C)


end DomainTheory.NeighbourhoodSystems.Exercise222

namespace DomainTheory.NeighbourhoodSystems.Exercise222

set_option linter.unusedVariables false

theorem example_222.{u_1} : ∀ {τ : Type u_1} (C : Set (Set τ))
  (hInter :
    ∀ (𝒮 : Set (Set τ)),
      @Set.Nonempty (Set τ) 𝒮 →
        @LE.le (Set (Set τ)) (@Set.instLE (Set τ)) 𝒮 C →
          @Membership.mem (Set τ) (Set (Set τ)) (@Set.instMembership (Set τ)) C (@Set.sInter τ 𝒮))
  (hne : @Set.Nonempty (Set τ) C)
  (hDir :
    ∀ (𝒮 : Set (Set τ)),
      @Set.Nonempty (Set τ) 𝒮 →
        @LE.le (Set (Set τ)) (@Set.instLE (Set τ)) 𝒮 C →
          @DirectedOn (Set τ) (fun (x1 x2 : Set τ) => @LE.le (Set τ) (@Set.instLE τ) x1 x2) 𝒮 →
            @Membership.mem (Set τ) (Set (Set τ)) (@Set.instMembership (Set τ)) C (@Set.sUnion τ 𝒮))
  (x :
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
      (@DomainTheory.NeighbourhoodSystems.Exercise222.Tok τ C)
      (@DomainTheory.NeighbourhoodSystems.Exercise222.reprSystem τ C hInter hne)),
  @Eq
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
      (@DomainTheory.NeighbourhoodSystems.Exercise222.Tok τ C)
      (@DomainTheory.NeighbourhoodSystems.Exercise222.reprSystem τ C hInter hne))
    (@DomainTheory.NeighbourhoodSystems.Exercise222.ofC τ C hInter hne
      (@DomainTheory.NeighbourhoodSystems.Exercise222.toC τ C hInter hne x)
      (@DomainTheory.NeighbourhoodSystems.Exercise222.toC_mem τ C hInter hne hDir x))
    x :=
  @DomainTheory.NeighbourhoodSystems.Exercise222.ofC_toC

end DomainTheory.NeighbourhoodSystems.Exercise222
