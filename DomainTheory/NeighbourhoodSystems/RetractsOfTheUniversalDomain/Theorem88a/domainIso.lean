/-ai
The elements of D are order-isomorphic to the elements of the embedded neighbourhood system, by the map into the embedded system with inverse the map back to D. In one round trip, a neighbourhood of the composite is an index whose embedded set equals the neighbourhood and a second index at which the enumerated neighbourhoods agree as embedded sets; equality of the embeddings rewrites membership of the second enumerated neighbourhood. Conversely, the cover writes a neighbourhood of the original element as an enumerated set, and the same index serves on both sides. The other round trip is the same argument with the equality of embeddings read in the opposite direction, the index now coming from membership in the embedded element. If the images are ordered, a neighbourhood of the smaller element is an enumerated set, the image inequality supplies a later index whose enumerated neighbourhood belongs to the larger element, and equality of embeddings rewrites it. An inequality of elements sends the enumerated witness of an embedded neighbourhood to a witness of the same index.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.splitChoice_isSplitSpec
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import Mathlib.Basic.Countable.Defs
import all Mathlib.Basic.Countable.Defs
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.mem_idxSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.Yidx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.embed_eq_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.DprimeU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.toDprimeU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.toD

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

section Iso

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

/-- **The order isomorphism `D.Element ≃o D'.Element`.** `toDprimeU`/`toD` are mutually inverse
(via `embed_eq_iff`, which resolves the ambiguity of *which* index represents a given
neighbourhood) and preserve/reflect `≤` (via `hcover`, which shows every `D`-neighbourhood a
filter can mention is literally some `e n`). -/
noncomputable def domainIso : DomainIso D (DprimeU D e hcover he0) where
  toFun := toDprimeU D e hcover he0
  invFun := toD D e hcover he0
  left_inv x := by
    apply Element.ext
    intro S
    constructor
    · rintro ⟨n, hn, k, hk, hxk⟩
      rw [hn, (embed_eq_iff e n k).mpr hk]
      exact hxk
    · intro hS
      obtain ⟨n, hn⟩ := (hcover S).mp (x.sub hS)
      refine ⟨n, hn, n, rfl, ?_⟩
      rwa [← hn]
  right_inv y := by
    apply Element.ext
    intro Y
    constructor
    · rintro ⟨n, hn, k, hk, hyk⟩
      rw [hn, (embed_eq_iff e n k).mp hk]
      exact hyk
    · intro hY
      obtain ⟨n, hn⟩ := y.sub hY
      refine ⟨n, hn, n, rfl, ?_⟩
      rwa [← hn]
  map_rel_iff' := by
    intro x x2
    constructor
    · intro hle S hxS
      obtain ⟨n, hn⟩ := (hcover S).mp (x.sub hxS)
      have hxn : x.mem (e n) := hn ▸ hxS
      obtain ⟨k, hk, hx2k⟩ := hle _ (⟨n, rfl, hxn⟩ : (toDprimeU D e hcover he0 x).mem (Yidx e n))
      rw [hn, (embed_eq_iff e n k).mpr hk]
      exact hx2k
    · intro hle Y hY
      obtain ⟨n, hn, hxn⟩ := hY
      exact ⟨n, hn, hle _ hxn⟩

end Iso

end DomainTheory.NeighbourhoodSystems
