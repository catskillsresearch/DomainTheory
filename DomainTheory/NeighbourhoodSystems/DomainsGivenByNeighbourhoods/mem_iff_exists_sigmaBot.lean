module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.sigmaBot_le_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.BitDom

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem mem_iff_exists_sigmaBot (x : B.Element) {Z : Set Str} :
    x.mem Z ↔ ∃ σ, x.mem (cone σ) ∧ (sigmaBot σ).mem Z := by
  constructor
  · intro hZ
    obtain ⟨σ, rfl⟩ := x.sub hZ
    exact ⟨σ, hZ, x.sub hZ, subset_rfl⟩
  · rintro ⟨σ, hcone, hZmem, hsub⟩
    exact x.up_mem hcone hZmem hsub

end DomainTheory.NeighbourhoodSystems.BitDom
