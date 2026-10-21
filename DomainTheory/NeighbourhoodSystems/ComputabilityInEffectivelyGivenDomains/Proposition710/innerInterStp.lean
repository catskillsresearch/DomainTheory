/-ai
One step of the inner fold reads the packed state as the current index, the accumulator, and the outer index. If the consistency test of the outer index with the current index returns one, the step returns the list code obtained by prepending their intersection index to the accumulator; otherwise it returns the accumulator.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

/-- One step of the **inner** fold (over `decodeList m`, parameter the outer index `a`): prepend
`P.inter a b` to the accumulator code iff `(a, b)` is consistent (`cons ⟨a,b⟩ = 1`), else leave it.
`foldCode` shape: state `w = ⟨b, ⟨acc, a⟩⟩`. -/
def innerInterStp (cons : ℕ → ℕ) (w : ℕ) : ℕ :=
  selectFn (isOne (cons (Nat.pair w.unpair.2.unpair.2 w.unpair.1)))
    (Nat.pair (P.inter w.unpair.2.unpair.2 w.unpair.1) w.unpair.2.unpair.1 + 1)
    w.unpair.2.unpair.1

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
