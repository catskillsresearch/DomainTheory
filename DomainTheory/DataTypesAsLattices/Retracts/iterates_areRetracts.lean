module

public import DomainTheory.DataTypesAsLattices.FixedPoint.iterateBot
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.bot_isRetract

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem iterates_areRetracts {F : Pomega → Pomega}
    (hret : ∀ a, Retract a → Retract (F a)) :
    ∀ n, Retract (iterateBot F n)
  | 0 => by simpa [iterateBot] using bot_isRetract
  | n + 1 => by simpa [iterateBot] using hret _ (iterates_areRetracts hret n)

end DomainTheory.DataTypesAsLattices
