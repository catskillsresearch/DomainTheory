module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}


section Smash


/-- **The subsystem relation `Exercise510.smash D E ◁ prod D E`.** Every smash neighbourhood is a
product neighbourhood; a proper smash neighbourhood stays proper (hence smash-membership, not just
product-membership) after any consistent intersection, by `Exercise510.inter_ne_master_left/right`
exactly as in `Exercise510.smash`'s own closure proof. -/
theorem smash_subsystem_prod : Exercise510.smash D E ◁ prod D E where
  master_eq := by rw [Exercise510.smash_master, prod_master]
  sub := by
    rintro W (rfl | ⟨X, Y, hX, -, hY, -, rfl⟩)
    · exact prod_mem_prodNbhd D.master_mem E.master_mem
    · exact prod_mem_prodNbhd hX hY
  inter_closed := by
    rintro W W' (rfl | ⟨X, Y, hX, hXne, hY, hYne, rfl⟩) hW' hPint
    · -- `W = smash master = prod master`.
      rcases hW' with rfl | ⟨X', Y', hX', hX'ne, hY', hY'ne, rfl⟩
      · left; rw [Set.inter_self]
      · right
        refine ⟨X', Y', hX', hX'ne, hY', hY'ne, ?_⟩
        rw [prodNbhd_inter, Set.inter_eq_right.mpr (D.sub_master hX'),
          Set.inter_eq_right.mpr (E.sub_master hY')]
    · -- `W = prodNbhd X Y` proper.
      rcases hW' with rfl | ⟨X', Y', hX', hX'ne, hY', hY'ne, rfl⟩
      · right
        refine ⟨X, Y, hX, hXne, hY, hYne, ?_⟩
        rw [prodNbhd_inter, Set.inter_eq_left.mpr (D.sub_master hX),
          Set.inter_eq_left.mpr (E.sub_master hY)]
      · -- both proper: `hPint` supplies the membership of the intersection in `prod D E`.
        rw [prodNbhd_inter] at hPint ⊢
        obtain ⟨hXX'mem, hYY'mem⟩ := prod_mem_prodNbhd_iff.mp hPint
        exact Or.inr ⟨X ∩ X', Y ∩ Y', hXX'mem, Exercise510.inter_ne_master_left hX hXne, hYY'mem,
          Exercise510.inter_ne_master_right hY hYne, rfl⟩

end Smash
end DomainTheory.NeighbourhoodSystems
