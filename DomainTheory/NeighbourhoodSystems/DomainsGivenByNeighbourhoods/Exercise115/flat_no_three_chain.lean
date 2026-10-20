module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.flat_classify
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.flat_atom_maximal

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem








/-- **Flat has no strict 3-chain** (`a ⊏ b ⊏ c` is impossible): `⊥` is least and atoms are maximal. -/
theorem flat_no_three_chain : ¬ ∃ a b c : flat.Element, a < b ∧ b < c := by
  rintro ⟨a, b, c, hab, hbc⟩
  rcases flat_classify b with rfl | ⟨n, rfl⟩
  · exact absurd (le_antisymm hab.le (flat.bot_le a)) (ne_of_lt hab)
  · exact (ne_of_lt hbc) (flat_atom_maximal n c hbc.le).symm

end DomainTheory.NeighbourhoodSystems.Exercise115
