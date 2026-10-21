/-ai
One step of the inner fold adds exactly the intersection of the two down-sets. When the consistency decider accepts the pair, the step prepends the intersection index; when it rejects the pair, that intersection of down-sets is empty and the accumulator is left unchanged. The case split is an equality of natural numbers.

If the decider returns 1, selection takes the successor pairing code. Its enumeration is the down-set of the intersection index united with the accumulator, and the intersection specification together with the down-set intersection law identifies that down-set. If the decider does not return 1, the one-test is at most 1 and is not 1, so it is 0, selection leaves the accumulator, and the intersection of the down-sets is empty.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd_cons_code
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.upSet_inter_eq_empty_of_not_cons

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

/-- One inner step at the `Ypd` level: prepending the consistent intersection index adds exactly
`↓X_a ∩ ↓X_b` (which is `∅` for inconsistent pairs). The `by_cases` on `cons ⟨a,b⟩ = 1` is on a
*decidable* `ℕ`-equality — choice-free. -/
theorem Ypd_innerstep (cons : ℕ → ℕ) {a b : ℕ}
    (hcons : cons (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b) (acc : ℕ) :
    V.Ypd P (selectFn (isOne (cons (Nat.pair a b))) (Nat.pair (P.inter a b) acc + 1) acc)
      = V.Ypd P acc ∪ (V.upSet (P.X a) ∩ V.upSet (P.X b)) := by
  by_cases h : cons (Nat.pair a b) = 1
  · rw [(isOne_eq_one_iff _).mpr h, selectFn_one, V.Ypd_cons_code P]
    have hXeq : P.X (P.inter a b) = P.X a ∩ P.X b := P.inter_spec (hcons.mp h)
    rw [hXeq, ← V.upSet_inter, Set.union_comm]
  · have hisz : isOne (cons (Nat.pair a b)) = 0 := by
      have hle := isOne_le_one (cons (Nat.pair a b))
      rcases (show isOne (cons (Nat.pair a b)) = 0 ∨ isOne (cons (Nat.pair a b)) = 1 by omega)
        with h0 | h1
      · exact h0
      · exact absurd ((isOne_eq_one_iff _).mp h1) h
    rw [hisz, selectFn_zero,
      V.upSet_inter_eq_empty_of_not_cons P (fun hk => h (hcons.mpr hk)), Set.union_empty]

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
