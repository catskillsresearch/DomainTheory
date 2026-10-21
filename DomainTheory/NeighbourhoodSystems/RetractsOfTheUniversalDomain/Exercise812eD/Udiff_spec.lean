/-ai
Whenever the difference of two U-neighbourhoods is itself a neighbourhood, the canonical neighbourhood at the difference index equals that difference.

The raw intervals of the difference index equal the difference, so they form a neighbourhood. Canonicalizing a list that already presents a neighbourhood leaves the presented intervals unchanged.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812eD.Udiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812eD.Udiff_eq_diff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`Udiff n m` genuinely indexes `UX n \ UX m` whenever that difference is a genuine
neighbourhood** — mirrors `Uinter_spec` exactly: the raw `diffCode` output is already a genuine
`U`-neighbourhood (by hypothesis via `Udiff_eq_diff`), so re-canonicalizing it (`canonCode`'s own
lookup, `UX`'s definition) is a no-op (`canonList_fixed`). -/
theorem Udiff_spec {n m : ℕ} (h : ∃ k, UX k = UX n \ UX m) : UX (Udiff n m) = UX n \ UX m := by
  have hUL : U.mem (presentedIntervals (decodeQPairList (Udiff n m))) := by
    rw [Udiff_eq_diff]
    obtain ⟨k, hk⟩ := h
    rw [← hk]; exact U_mem_UX k
  show presentedIntervals (decodeQPairList (canonCode (Udiff n m))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL, Udiff_eq_diff]

end DomainTheory.NeighbourhoodSystems
