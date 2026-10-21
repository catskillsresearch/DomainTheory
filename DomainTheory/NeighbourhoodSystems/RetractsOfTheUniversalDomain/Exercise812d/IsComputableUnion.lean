/-ai
IsComputableUnion says that set union is computable relative to a presentation. It provides a primitive-recursive index of the union of the n-th and m-th neighbourhoods whenever that union is itself some neighbourhood of the presentation, together with a recursive decider for that side condition.
ai-/
module


public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

/-- **`IsComputableUnion P`**: set-union relative to the presentation `P` is computable — a
primitive-recursive `unionIdx : ℕ → ℕ → ℕ` indexing `X n ∪ X m` whenever that union is a genuine
neighbourhood (`unionIdx_spec`, mirroring `inter_spec`/`IsComputableDiff.diffIdx_spec` exactly),
together with a decider for that side-condition (`union_computable`, mirroring
`cons_computable`/`IsComputableDiff.diff_computable`). Only `unionIdx` is data; the rest are
`Prop`s, so this stays choice-free to *state* (any particular instance may of course need
`Classical.choice` to *construct*, exactly like `inter`/`cons_computable`/`IsComputableDiff`
themselves would for an arbitrary effectively-given system). -/
structure IsComputableUnion {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
    where
  /-- Index of `X n ∪ X m`, as a function of the two input indices. -/
  unionIdx : ℕ → ℕ → ℕ
  /-- `unionIdx` is primitive recursive (on the `Nat.pair` coding of `n, m`). -/
  unionIdx_primrec : Nat.Primrec (fun t => unionIdx t.unpair.1 t.unpair.2)
  /-- `unionIdx n m` genuinely indexes `X n ∪ X m` whenever that union is (exactly) some `X k` —
  i.e. whenever it is a genuine neighbourhood. -/
  unionIdx_spec : ∀ {n m : ℕ}, (∃ k, P.X k = P.X n ∪ P.X m) → P.X (unionIdx n m) = P.X n ∪ P.X m
  /-- **7.1(i)-for-`∪`**: "`X n ∪ X m` is a genuine neighbourhood" is recursively decidable in
  `n, m`, mirroring `cons_computable`'s role for `∩`. -/
  union_computable : RecDecidable₂ (fun n m => ∃ k, P.X k = P.X n ∪ P.X m)

end DomainTheory.NeighbourhoodSystems
