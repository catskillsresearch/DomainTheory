module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}


variable (V : NeighborhoodSystem α)


/-- **Exercise 3.26(i) (Scott 1981, PRG-19).** `cond(true, x, y) = x`. -/
theorem cond_true (x y : V.Element) :
    (cond V).toElementMap (pair Example23.trueElt (pair x y)) = x := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨W, hWmem, _, hZ, hg⟩
    obtain ⟨C, P, hCtrue, hPmem, rfl⟩ := hWmem
    obtain ⟨X, Y, hXx, hYy, rfl⟩ := hPmem
    simp only [condGuard, inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hg
    rcases hg with ⟨_, hXZ⟩ | ⟨hCo, _⟩ | ⟨_, hmZ⟩
    · exact x.up_mem hXx hZ hXZ
    · rcases hCtrue with hCm | hCz
      · exact absurd (hCm.symm.trans hCo) one_ne_master.symm
      · exact absurd (hCz.symm.trans hCo) zero_ne_one
    · rw [Set.Subset.antisymm (V.sub_master hZ) hmZ]; exact x.master_mem
  · intro hxZ
    have hZ : V.mem Z := x.sub hxZ
    refine ⟨prodNbhd Example12.zero (prodNbhd Z V.master), ⟨Example12.zero, prodNbhd Z V.master,
      Or.inr rfl, ⟨Z, V.master, hxZ, y.master_mem, rfl⟩, rfl⟩,
      prod_mem_prodNbhd Example12.mem_zero (prod_mem_prodNbhd hZ V.master_mem), hZ, ?_⟩
    refine Or.inl ⟨inl_preimage_prodNbhd _ _, ?_⟩
    rw [inr_preimage_prodNbhd, inl_preimage_prodNbhd]

end DomainTheory.NeighbourhoodSystems.Exercise326
