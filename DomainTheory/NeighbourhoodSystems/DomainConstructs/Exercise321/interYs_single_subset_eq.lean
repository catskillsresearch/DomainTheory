module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- For a single step `[Y, Z]` and a *sharp enough* input `X ⊆ Y`, the intersection is just `Z`. -/
theorem interYs_single_subset_eq {YX : Set α} {Z : Set β} {X : Set α} (hZ : V₁.mem Z)
    (hXY : X ⊆ YX) : interYs V₁.master [(YX, Z)] X = Z := by
  ext z
  rw [mem_interYs]
  constructor
  · rintro ⟨_, hall⟩; exact hall (YX, Z) (List.mem_singleton.mpr rfl) hXY
  · intro hz
    exact ⟨V₁.sub_master hZ hz, fun p hp _ => by rw [List.mem_singleton] at hp; subst hp; exact hz⟩

end DomainTheory.NeighbourhoodSystems
