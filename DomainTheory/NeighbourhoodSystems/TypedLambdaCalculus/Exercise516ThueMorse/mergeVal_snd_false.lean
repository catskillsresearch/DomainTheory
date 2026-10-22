module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import Mathlib.Data.Nat.Bits
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419


/-- The second (total/partial-flag) component of an interleaving with a partial first input is always
`false`: a partial input keeps the output partial. -/
theorem mergeVal_snd_false : ∀ (σ τ : Str) (b₁ : Bool), (mergeVal σ false τ b₁).2 = false
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: σ, _ :: τ, b₁ => by simp only [mergeVal_cons_cons]; exact mergeVal_snd_false σ τ b₁

end DomainTheory.NeighbourhoodSystems.Exercise516
