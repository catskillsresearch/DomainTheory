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
  | n + 1 => IsScottContinuous.monotone hf (iterateFrom_mono hf hx n)

end DomainTheory.DataTypesAsLattices
