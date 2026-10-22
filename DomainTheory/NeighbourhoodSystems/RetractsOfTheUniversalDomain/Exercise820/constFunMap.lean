module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u v

section FunSpace

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)

/-- **`b ↦ (λ_. b)`, the constant-function embedding.** `curry (proj₀ B A) : B → (A → B)` sends `b`
to the function that ignores its argument and always returns `b`. -/
noncomputable def constFunMap : ApproximableMap B (funSpace A B) := curry (proj₀ B A)

end FunSpace

end DomainTheory.NeighbourhoodSystems
