module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}







variable {D : ∀ i, NeighborhoodSystem (α i)}
















/-- **Exercise 6.29 — a sum element reaches at most one summand.** -/
theorem isum_summand_unique {hne : ∀ i, ∀ X : Set (α i), (D i).mem X → X.Nonempty}
    (z : (isum D hne).Element) {i j : ι} {X : Set (α i)} {Y : Set (α j)}
    (hX : z.mem (injI i X)) (hY : z.mem (injI j Y)) : i = j := by
  -- The filter element `z` contains the consistent intersection; its representative carries a
  -- token whose index is forced to be both `i` and `j` — no excluded middle on `i = j`.
  have hz := z.inter_mem hX hY
  rcases z.sub hz with h0 | ⟨k, W, hWmem, hWeq⟩
  · rw [Set.ext_iff] at h0
    exact absurd ((h0 none).mpr none_mem_sumMasterI).1 none_not_mem_injI
  · obtain ⟨w, hw⟩ := hne k W hWmem
    rw [Set.ext_iff] at hWeq
    have hmem := (hWeq (some ⟨k, w⟩)).mpr (some_mem_injI.mpr hw)
    obtain rfl := index_of_some_mem_injI hmem.1
    obtain rfl := index_of_some_mem_injI hmem.2
    rfl

end Exercise629
end DomainTheory.NeighbourhoodSystems
