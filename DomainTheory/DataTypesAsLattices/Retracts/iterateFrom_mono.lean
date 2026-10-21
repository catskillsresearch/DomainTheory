/-ai
If a Scott-continuous map lies above its starting set, its directed iterates are increasing.

The first inclusion is the hypothesis that the starting set lies below its image. Each later inclusion is monotonicity of the map applied to the preceding inclusion.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.iterateFrom

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem iterateFrom_mono {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {x : Pomega} (hx : x ⊆ f x) :
    ∀ n, iterateFrom f x n ⊆ iterateFrom f x (n + 1)
  | 0 => hx
  | n + 1 => isScottContinuous_monotone hf (iterateFrom_mono hf hx n)

end DomainTheory.DataTypesAsLattices
