/-ai
If f is Scott continuous, each iterate of f from the bottom element is contained in the next iterate.

The inclusion at zero is emptiness of the bottom element. The successor inclusion is monotonicity of f applied to the inductive inclusion.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Graph
public import DomainTheory.DataTypesAsLattices.FixedPoint.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices



theorem iterateBot_mono {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    ∀ n, iterateBot f n ⊆ iterateBot f (n + 1)
  | 0 => by
    simp [iterateBot, botElem]
  | n + 1 =>
    isScottContinuous_monotone hf (iterateBot_mono hf n)

end DomainTheory.DataTypesAsLattices
