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
