/-ai
The map sub f relates the presented neighbourhoods of indices a and b exactly when some presented neighbourhood is related to itself by f and lies between them.

Both presented sets are neighbourhoods. A witness neighbourhood of the relation of sub is some presented set by surjectivity of the presentation. Conversely, a presented witness is a neighbourhood together with the self-relation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86c.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Sub8_6

variable {α : Type*} {E : NeighborhoodSystem α}


section SubComputable

variable (P : ComputablePresentation E) (gN : ℕ → ℕ)
  (hgN : ∀ c, gN c = 1 ↔
    (stepFun (funListOf P P (decodeList c)) : Set (ApproximableMap E E)).Nonempty)

/-- **`sub`'s defining existential, reindexed to presentation indices.** `sub f` relates presented
neighbourhoods `X_a`, `X_b` iff some presented `X_y` witnesses Scott's formula (`P.surj` turns the
arbitrary witness neighbourhood `Y` of `sub_rel` into an index `y`). -/
theorem sub_rel_iff_exists_index {f : ApproximableMap E E} {a b : ℕ} :
    (sub f).rel (P.X a) (P.X b) ↔
      ∃ y : ℕ, f.rel (P.X y) (P.X y) ∧ P.X a ⊆ P.X y ∧ P.X y ⊆ P.X b := by
  rw [sub_rel, and_iff_right (P.mem_X a), and_iff_right (P.mem_X b)]
  constructor
  · rintro ⟨Y, ⟨hYE, hYf⟩, haY, hYb⟩
    obtain ⟨y, rfl⟩ := P.surj hYE
    exact ⟨y, hYf, haY, hYb⟩
  · rintro ⟨y, hYf, haY, hYb⟩
    exact ⟨P.X y, ⟨P.mem_X y, hYf⟩, haY, hYb⟩

end SubComputable
end DomainTheory.NeighbourhoodSystems
