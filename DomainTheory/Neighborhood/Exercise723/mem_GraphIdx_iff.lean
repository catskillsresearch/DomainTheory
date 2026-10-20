/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example78
import DomainTheory.Neighborhood.Theorem74
import DomainTheory.Neighborhood.Theorem75
import DomainTheory.Neighborhood.Exercise514
import DomainTheory.Neighborhood.Exercise723.Basic
import DomainTheory.Neighborhood.Exercise723.tagOfBits_spec
import DomainTheory.Neighborhood.Exercise723.tag_untagList_untagVal
import DomainTheory.Neighborhood.Exercise723.decodeList_injective


namespace DomainTheory.Neighborhood.Exercise723

open DomainTheory.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
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

end DomainTheory.Neighborhood.Exercise723
