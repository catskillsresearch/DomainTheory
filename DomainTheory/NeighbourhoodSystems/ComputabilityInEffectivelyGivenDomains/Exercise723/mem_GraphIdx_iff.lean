/-ai
A code c lies in GraphIdx W if and only if there exist n and m₀ such that the untagged list of c equals bitsCode n n, every map in W relates nbhd n to nbhd m₀, and the bit of m₀ at the untagged value of c is set. Tagging the decoded bit list is one encoding of the pair consisting of the excluded set and a value, and decoding recovers it.

From a witness n, m₀, and m with c equal to tagOfBits n m, the untagging round trip composed with the specification of tagOfBits is a tagging equality. Injectivity of tagging splits it into a list equality and a value equality, injectivity of decoding gives the bit-code equation, and rewriting the bit by the value equality keeps the bit hypothesis. Conversely, the untagged value is the missing third component, and the specification of tagOfBits together with the symmetric untagging round trip recover the code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.tagOfBits_spec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.tag_untagList_untagVal
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.decodeList_injective

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)










































































/-- **`GraphIdx` membership, decoded.** `tagOfBits n m = tag (decodeList (bitsCode n n)) m` is a
*specific* choice of encoding for the pair `(Eₙ, m)`; since `tag` is injective and every code `c`
decodes (via `untagList`/`untagVal`) to *some* `tag`-preimage, `c ∈ GraphIdx W` reduces to the
primitive-recursive check `untagList c = bitsCode n n` (pinning down `n`, by injectivity of
`decodeList`) together with `untagVal c` playing the role of `m`. -/
theorem mem_GraphIdx_iff (W : Set (ApproximableMap PN PN)) (c : ℕ) :
    c ∈ GraphIdx W ↔ ∃ n m₀, untagList c = bitsCode n n ∧
      (∀ f ∈ W, f.rel (nbhd n) (nbhd m₀)) ∧ m₀.testBit (untagVal c) = true := by
  constructor
  · rintro ⟨n, m₀, m, rfl, hf, hbit⟩
    have htag : tag (decodeList (untagList (tagOfBits n m))) (untagVal (tagOfBits n m)) =
        tag (decodeList (bitsCode n n)) m :=
      (tag_untagList_untagVal (tagOfBits n m)).trans (tagOfBits_spec n m)
    obtain ⟨hlist, hval⟩ := tag_injective htag
    refine ⟨n, m₀, decodeList_injective hlist, hf, ?_⟩
    rw [hval]; exact hbit
  · rintro ⟨n, m₀, heq, hf, hbit⟩
    refine ⟨n, m₀, untagVal c, ?_, hf, hbit⟩
    rw [tagOfBits_spec, ← heq]
    exact (tag_untagList_untagVal c).symm

end DomainTheory.NeighbourhoodSystems.Exercise723
