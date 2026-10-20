module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import Mathlib.Data.Nat.Bits
import all Mathlib.Data.Nat.Bits
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.weave_head
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tmOp_strBot

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419







/-- **The Thue–Morse trajectory.** On a partial element whose string starts with `0`, `Φ` acts as the
Thue–Morse morphism `expand`. -/
theorem tmOp_strBot_expand (ρ : Str) :
    tmOp.toElementMap (strBot (false :: ρ)) = strBot (expand (false :: ρ)) := by
  rw [tmOp_strBot]
  simp only [flip_cons, List.tail_cons, expand_cons]
  rw [weave_head (!false) ρ]

end DomainTheory.NeighbourhoodSystems.Exercise516
