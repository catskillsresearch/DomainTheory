/-ai
If a binary relation is recursively enumerable, then so is the predicate of a packed parameter and list code which says that the relation holds of the parameter and every entry of the decoded list.

The paired form of the relation is recursively enumerable, so the unparameterised bounded universal quantification of that predicate over a decoded list is recursively enumerable, and reindexing along the pair-map of codes preserves enumerability. Decoding the mapped code is the reverse of the list of pairs, so an entry of the mapped list is the pair of the parameter with an entry of the original list, and both directions of the quantifier rewrite by that correspondence.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.decodeList_mapPairCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.primrec_mapPairCode

@[expose] public section


namespace Domain.Recursive


/-- **Parameterised bounded `∀` over a coded list preserves recursive enumerability.** If `p` is an
r.e. binary relation then `fun t => ∀ e ∈ decodeList t.2, p t.1 e` is r.e.: re-code the list into the
pairs `⟨t.1, e⟩` (`mapPairCode`) and apply the unparameterised `forall_mem_decodeList`. -/
theorem REPred.forall_mem_decodeList₂ {p : ℕ → ℕ → Prop} (hp : REPred₂ p) :
    REPred (fun t => ∀ e ∈ decodeList t.unpair.2, p t.unpair.1 e) := by
  have hp' : REPred (fun s => p s.unpair.1 s.unpair.2) := hp
  have hbase : REPred (fun c => ∀ e' ∈ decodeList c, p e'.unpair.1 e'.unpair.2) :=
    hp'.forall_mem_decodeList
  refine REPred.of_iff (fun t => ?_) (hbase.comp primrec_mapPairCode)
  rw [decodeList_mapPairCode]
  simp only [List.mem_reverse, List.mem_map]
  constructor
  · rintro hall e' ⟨e, he, rfl⟩
    simp only [unpair_pair_fst, unpair_pair_snd]
    exact hall e he
  · intro hall e he
    simpa only [unpair_pair_fst, unpair_pair_snd]
      using hall (Nat.pair t.unpair.1 e) ⟨e, he, rfl⟩

end Domain.Recursive
