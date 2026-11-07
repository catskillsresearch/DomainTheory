module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.endofunctor

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

/-- Scott's Definition 6.3: an endofunctor assigns `T(X)` and `T(f)`, preserving identity
and composition. -/
theorem definition_63 {Obj : Type u} [Category Obj] (T : Endofunctor Obj) :
    (∀ X : Obj, T.map (𝟙 X) = 𝟙 (T.obj X)) ∧
      (∀ {X Y Z : Obj} (f : X ⟶ Y) (g : Y ⟶ Z), T.map (g ⊚ f) = T.map g ⊚ T.map f) :=
  ⟨fun X => T.map_id X, @fun _ _ _ f g => T.map_comp (g := g) (f := f)⟩

end DomainTheory.NeighbourhoodSystems
