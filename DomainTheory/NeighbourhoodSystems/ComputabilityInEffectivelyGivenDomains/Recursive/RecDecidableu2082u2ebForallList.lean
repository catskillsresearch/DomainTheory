/-ai
If a binary relation is recursively decidable, then so is the relation of a list code and a parameter which says that every entry of the decoded list stands in the relation to the parameter.

The characteristic is the list-universal character of the binary decider. It is primitive recursive, and it equals one exactly when every entry satisfies the relation, because that character lemma matches the decider on pairs.
ai-/
module

public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.List.Basic
public import Mathlib.Computability.Partrec
public import Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.primrec_allListChar

@[expose] public section


namespace Domain.Recursive


/-- **Bounded `∀` over a coded list preserves recursive decidability.** If `q` is a recursively
decidable binary relation then `fun c p => ∀ e ∈ decodeList c, q e p` is too (the list is coded by
the first argument, `p` is a free parameter). Choice-free. -/
theorem RecDecidable₂.bForallList {q : ℕ → ℕ → Prop} (hq : RecDecidable₂ q) :
    RecDecidable₂ (fun c p => ∀ e ∈ decodeList c, q e p) := by
  obtain ⟨g, hgp, hgs⟩ := hq
  refine ⟨fun t => allListChar g t.unpair.2 t.unpair.1, primrec_allListChar hgp, fun t => ?_⟩
  show (∀ e ∈ decodeList t.unpair.1, q e t.unpair.2) ↔ allListChar g t.unpair.2 t.unpair.1 = 1
  rw [allListChar_eq_one_iff]
  refine forall_congr' fun e => forall_congr' fun _ => ?_
  have := hgs (Nat.pair e t.unpair.2)
  simp only [unpair_pair_fst, unpair_pair_snd] at this
  exact this

end Domain.Recursive
