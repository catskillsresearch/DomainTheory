module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.C_dir

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


end DomainTheory.NeighbourhoodSystems.Exercise327

namespace DomainTheory.NeighbourhoodSystems.Exercise327

set_option linter.unusedVariables false

theorem example_327.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} (𝒮 : Set (Set (Prod (Set α) (Set β)))),
  @Set.Nonempty (Set (Prod (Set α) (Set β))) 𝒮 →
    @LE.le (Set (Set (Prod (Set α) (Set β)))) (@Set.instLE (Set (Prod (Set α) (Set β)))) 𝒮
        (@DomainTheory.NeighbourhoodSystems.Exercise327.C α β V₀ V₁) →
      @DirectedOn (Set (Prod (Set α) (Set β)))
          (fun (x1 x2 : Set (Prod (Set α) (Set β))) =>
            @LE.le (Set (Prod (Set α) (Set β))) (@Set.instLE (Prod (Set α) (Set β))) x1 x2)
          𝒮 →
        @Membership.mem (Set (Prod (Set α) (Set β))) (Set (Set (Prod (Set α) (Set β))))
          (@Set.instMembership (Set (Prod (Set α) (Set β))))
          (@DomainTheory.NeighbourhoodSystems.Exercise327.C α β V₀ V₁) (@Set.sUnion (Prod (Set α) (Set β)) 𝒮) :=
  @DomainTheory.NeighbourhoodSystems.Exercise327.C_dir

end DomainTheory.NeighbourhoodSystems.Exercise327
