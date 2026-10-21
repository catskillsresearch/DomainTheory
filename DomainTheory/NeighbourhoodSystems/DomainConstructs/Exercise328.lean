/-ai
The least map at an element equals the supremum of the active principal filters at that element.

The numbered name example_328 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise328.toElementMap_leastMap_eq_sSup

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_328.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} (L : List (Prod (Set α) (Set β)))
  (hL :
    ∀ (p : Prod (Set α) (Set β)),
      @Membership.mem (Prod (Set α) (Set β)) (List (Prod (Set α) (Set β))) (@List.instMembership (Prod (Set α) (Set β)))
          L p →
        And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ (@Prod.fst (Set α) (Set β) p))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ (@Prod.snd (Set α) (Set β) p)))
  (hcons :
    ∀ {X : Set α},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁
          (@DomainTheory.NeighbourhoodSystems.interYs α β
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁) L X))
  (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀),
  @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
      (@DomainTheory.NeighbourhoodSystems.leastMap α β V₀ V₁ L hL fun {X : Set α} => @hcons X) x)
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup β V₁
      (@DomainTheory.NeighbourhoodSystems.leastMapVals α β V₀ V₁ L hL x)
      (@DomainTheory.NeighbourhoodSystems.leastMapVals_bounded α β V₀ V₁ L hL (fun {X : Set α} => @hcons X) x)) :=
  @DomainTheory.NeighbourhoodSystems.toElementMap_leastMap_eq_sSup

end DomainTheory.NeighbourhoodSystems
