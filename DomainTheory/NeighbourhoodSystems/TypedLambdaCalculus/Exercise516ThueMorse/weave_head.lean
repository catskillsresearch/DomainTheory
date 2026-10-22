module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import Mathlib.Data.Nat.Bits
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419


/-- The interleaving of `h :: flip ρ` with `ρ` (both starting after a common head `h`) is
`h :: expand ρ`. This is the heart of why `Φ` *is* the Thue–Morse morphism on the trajectory. -/
theorem weave_head : ∀ (h : Bool) (ρ : Str), (mergeVal (h :: flip ρ) false ρ false).1 = h :: expand ρ
  | h, [] => rfl
  | h, c :: ρ => by
    simp only [flip_cons, mergeVal_cons_cons, expand_cons]
    rw [weave_head (!c) ρ]

end DomainTheory.NeighbourhoodSystems.Exercise516
