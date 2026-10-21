/-ai
An output neighbourhood belongs to the conditional at a paired argument when the truth element contains zero and the output belongs to the first argument, or the truth element contains one and the output belongs to the second argument, or the output is the master.

A witnessing input splits as a product of a truth neighbourhood with neighbourhoods of the two arguments. The zero clause places zero in the truth element and the output above a neighbourhood of the first argument, the one clause does the same for one and the second argument, and the master clause forces the output to be the master. Conversely, the three alternatives are witnessed by the product of the singleton of zero with the output and the master, the product of the singleton of one with the master and the output, and the product of the three masters, with the corresponding guard clause given by the preimage computations.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}










variable (V : NeighborhoodSystem α)








/-- The elementwise action of `cond`, computed at a paired argument `⟨t, ⟨x, y⟩⟩`: a neighbourhood
`Z` lies in `cond(t, x, y)` iff `t` selects `true` (`{0} ∈ t`) and `Z ∈ x`, or `t` selects `false`
(`{1} ∈ t`) and `Z ∈ y`, or `Z = Δ_D` (the always-present master). The three defining identities are
immediate corollaries. -/
theorem cond_toElementMap_mem (t : TD.Element) (x y : V.Element) {Z : Set α} :
    ((cond V).toElementMap (pair t (pair x y))).mem Z ↔
      (t.mem Example12.zero ∧ x.mem Z) ∨ (t.mem Example12.one ∧ y.mem Z) ∨ Z = V.master := by
  constructor
  · rintro ⟨W, hWmem, _, hZ, hg⟩
    obtain ⟨C, P, hCt, hPmem, rfl⟩ := hWmem
    obtain ⟨X, Y, hXx, hYy, rfl⟩ := hPmem
    simp only [condGuard, inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hg
    rcases hg with ⟨hCz, hXZ⟩ | ⟨hCo, hYZ⟩ | ⟨_, hmZ⟩
    · exact Or.inl ⟨hCz ▸ hCt, x.up_mem hXx hZ hXZ⟩
    · exact Or.inr (Or.inl ⟨hCo ▸ hCt, y.up_mem hYy hZ hYZ⟩)
    · exact Or.inr (Or.inr (Set.Subset.antisymm (V.sub_master hZ) hmZ))
  · intro h
    rcases h with ⟨ht0, hxZ⟩ | ⟨ht1, hyZ⟩ | rfl
    · have hZ : V.mem Z := x.sub hxZ
      refine ⟨prodNbhd Example12.zero (prodNbhd Z V.master), ⟨Example12.zero, prodNbhd Z V.master,
        ht0, ⟨Z, V.master, hxZ, y.master_mem, rfl⟩, rfl⟩,
        prod_mem_prodNbhd Example12.mem_zero (prod_mem_prodNbhd hZ V.master_mem), hZ, ?_⟩
      refine Or.inl ⟨inl_preimage_prodNbhd _ _, ?_⟩
      rw [inr_preimage_prodNbhd, inl_preimage_prodNbhd]
    · have hZ : V.mem Z := y.sub hyZ
      refine ⟨prodNbhd Example12.one (prodNbhd V.master Z), ⟨Example12.one, prodNbhd V.master Z,
        ht1, ⟨V.master, Z, x.master_mem, hyZ, rfl⟩, rfl⟩,
        prod_mem_prodNbhd Example12.mem_one (prod_mem_prodNbhd V.master_mem hZ), hZ, ?_⟩
      refine Or.inr (Or.inl ⟨inl_preimage_prodNbhd _ _, ?_⟩)
      rw [inr_preimage_prodNbhd, inr_preimage_prodNbhd]
    · refine ⟨prodNbhd Example12.master (prodNbhd V.master V.master),
        ⟨Example12.master, prodNbhd V.master V.master, t.master_mem,
          ⟨V.master, V.master, x.master_mem, y.master_mem, rfl⟩, rfl⟩,
        prod_mem_prodNbhd Example12.mem_master (prod_mem_prodNbhd V.master_mem V.master_mem),
        V.master_mem, ?_⟩
      exact Or.inr (Or.inr ⟨inl_preimage_prodNbhd _ _, subset_rfl⟩)

end DomainTheory.NeighbourhoodSystems.Exercise326
