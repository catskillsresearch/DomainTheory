module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.mem_Ypd

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

/-- `↓X_a ⊆ Y_k ↔ ∃ b ∈ dl k, X_a ⊆ X_b` (a down-set lies in a finite union of down-sets iff its top
`X_a` is below one of them). -/
theorem upSet_subset_Ypd_iff {a k : ℕ} :
    V.upSet (P.X a) ⊆ V.Ypd P k ↔ ∃ b ∈ decodeList k, P.X a ⊆ P.X b := by
  constructor
  · intro h
    have hmem : P.X a ∈ V.Ypd P k := h ⟨P.mem_X a, subset_rfl⟩
    obtain ⟨b, hb, hPab⟩ := (V.mem_Ypd P).mp hmem
    exact ⟨b, hb, hPab.2⟩
  · rintro ⟨b, hb, hab⟩ z hz
    exact (V.mem_Ypd P).mpr ⟨b, hb, hz.1, hz.2.trans hab⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
