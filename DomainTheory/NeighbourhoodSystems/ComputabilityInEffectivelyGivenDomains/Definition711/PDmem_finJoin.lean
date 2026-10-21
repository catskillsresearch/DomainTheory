/-ai
A set W belongs to the finite join of a family of length n if and only if W is the master neighbourhood of the power domain when n is zero, and W satisfies the finite-join membership predicate otherwise.

Split on n. In the zero case, simplify by the empty join, the zero join, and membership in the bottom element. In the successor case, simplify by the finite join and the successor join.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)









theorem PDmem_finJoin {n : ℕ} (xs : Fin n → V.Element) {W : Set (Set α)} :
    (V.PDfinJoin n xs).mem W ↔
      if n = 0 then W = V.PowerDomain.master else V.PDmemFinJoin xs W := by
  match n with
  | 0 => simp [PDfinJoin, PDfinJoinZero, mem_bot]
  | m + 1 => simp [PDfinJoin, PDfinJoinSucc]

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
