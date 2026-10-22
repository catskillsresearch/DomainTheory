module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.halfIter_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.mem_elemSet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.tagOfBits
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic.notation16

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive

open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)

open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)

/-- `GraphIdx W`: the domain-theoretic "positive content" of `graph(W)`, mirroring Exercise 5.14's
`Graph f = {tag ns m ∣ m ∈ f (entries ns)}`, but phrased at the level of neighbourhood relations and
tested against *every* map `f ∈ W` (Scott's "guaranteed regardless of which `f ∈ W`" idiom, as in
`eval`'s `∀ f ∈ F, f.rel X Y`). The "argument" is canonically `tagOfBits n m = tag (decodeList
(bitsCode n n)) m` (`decodeList (bitsCode n n)` has entries exactly `Eₙ`, `mem_bitsCodeList`), so it
ranges over the countably many finite sets `(nbhd n)ᶜ` rather than over arbitrary lists — exactly the
finite-set arguments `Graph` needs, up to the reindexing already used throughout this file. Using the
*primitive-recursive* list `bitsCode n n` (rather than the merely well-founded `bitsList n`) is what
makes the decode direction (`mem_GraphIdx_iff` below) computable. -/
def GraphIdx (W : Set (ApproximableMap PN PN)) : Set ℕ :=
  {c | ∃ n m₀ m, c = tagOfBits n m ∧ (∀ f ∈ W, f.rel (nbhd n) (nbhd m₀)) ∧ m₀.testBit m = true}

end DomainTheory.NeighbourhoodSystems.Exercise723
