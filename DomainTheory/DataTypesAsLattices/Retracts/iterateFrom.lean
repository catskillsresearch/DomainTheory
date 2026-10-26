module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.FixedPoint.iterateBot

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Directed iterates of `f` starting from `x` (Scott's sup construction). -/
def iterateFrom (f : Pomega → Pomega) (x : Pomega) : ℕ → Pomega
  | 0 => x
  | n + 1 => f (iterateFrom f x n)

namespace iterateFrom

theorem bot (f : Pomega → Pomega) (n : ℕ) :
    iterateFrom f botElem n = iterateBot f n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iterateFrom, iterateBot, ih]

theorem mono {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {x : Pomega} (hx : x ⊆ f x) :
    ∀ n, iterateFrom f x n ⊆ iterateFrom f x (n + 1)
  | 0 => hx
  | n + 1 => IsScottContinuous.monotone hf (mono hf hx n)

end iterateFrom

end DomainTheory.DataTypesAsLattices
