/-ai
The conditional at bottom returns bottom.

If an output neighbourhood belongs to the value, the witnessing input splits as a product whose truth component belongs to bottom, hence is the master. The zero and one clauses of the guard contradict that, so the master of the codomain is contained in the output and the output is the master. Conversely, the product of the three master neighbourhoods lies in the paired argument and satisfies the master clause of the guard.
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








/-- **Exercise 3.26(iii) (Scott 1981, PRG-19).** `cond(⊥, x, y) = ⊥`. -/
theorem cond_bot (x y : V.Element) :
    (cond V).toElementMap (pair Example23.botElt (pair x y)) = V.bot := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨W, hWmem, _, hZ, hg⟩
    obtain ⟨C, P, hCbot, hPmem, rfl⟩ := hWmem
    obtain ⟨X, Y, hXx, hYy, rfl⟩ := hPmem
    simp only [condGuard, inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hg
    have hCm : C = Example12.master := hCbot
    rcases hg with ⟨hCz, _⟩ | ⟨hCo, _⟩ | ⟨_, hmZ⟩
    · exact absurd (hCm.symm.trans hCz) zero_ne_master.symm
    · exact absurd (hCm.symm.trans hCo) one_ne_master.symm
    · rw [mem_bot, Set.Subset.antisymm (V.sub_master hZ) hmZ]
  · intro hbZ
    rw [mem_bot] at hbZ
    subst hbZ
    refine ⟨prodNbhd Example12.master (prodNbhd V.master V.master),
      ⟨Example12.master, prodNbhd V.master V.master, rfl,
        ⟨V.master, V.master, x.master_mem, y.master_mem, rfl⟩, rfl⟩,
      prod_mem_prodNbhd Example12.mem_master (prod_mem_prodNbhd V.master_mem V.master_mem),
      V.master_mem, ?_⟩
    exact Or.inr (Or.inr ⟨inl_preimage_prodNbhd _ _, subset_rfl⟩)

end DomainTheory.NeighbourhoodSystems.Exercise326
