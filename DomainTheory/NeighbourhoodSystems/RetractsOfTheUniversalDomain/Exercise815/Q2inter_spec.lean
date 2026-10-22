module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_finGenSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nodeCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal_node
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q2X
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q2inter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section UniversalSubsystem

section TreeVal2

variable (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)

/-- **`inter_spec` for `Q2X r`.** The hypothesis is exactly what `Uinter_spec` needs (a `UX`-witness
of consistency, transported through `TreeVal`), so `nodeCode n m` genuinely indexes the intersection
— no fallback case to worry about. -/
theorem Q2inter_spec {n m : ℕ} (h : ∃ k, Q2X r k ⊆ Q2X r n ∩ Q2X r m) :
    Q2X r (Q2inter n m) = Q2X r n ∩ Q2X r m := by
  obtain ⟨k, hk⟩ := h
  show UX (TreeVal r (nodeCode n m)) = UX (TreeVal r n) ∩ UX (TreeVal r m)
  rw [TreeVal_node]
  exact Uinter_spec ⟨TreeVal r k, hk⟩

end TreeVal2

end UniversalSubsystem

end DomainTheory.NeighbourhoodSystems
