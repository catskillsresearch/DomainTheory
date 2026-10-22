module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.InS
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.mem_concat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Ssys
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Ssys_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.mem_mulElem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.mem_emb
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.repeatWord
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.repeatWord_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.mem_powerLang
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.streamElemMem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open NeighborhoodSystem ApproximableMap

/-- Scott's **`w⃗`** as a domain element. -/
def streamElem (w : List Bool) : Ssys.Element where
  mem Z := streamElemMem w Z
  sub h := h.1
  master_mem := ⟨InS.univ, fun n => Set.mem_univ (repeatWord w n)⟩
  inter_mem := by
    intro X Y hX hY
    obtain ⟨hXIn, hXw⟩ := hX
    obtain ⟨hYIn, hYw⟩ := hY
    exact ⟨InS.inter hXIn hYIn ⟨repeatWord w 0, hXw 0, hYw 0⟩, fun n => ⟨hXw n, hYw n⟩⟩
  up_mem := by
    intro X Y hX hInSY hsub
    obtain ⟨_hXIn, hXw⟩ := hX
    exact ⟨hInSY, fun n => hsub (hXw n)⟩

end Exercise722

end DomainTheory.NeighbourhoodSystems
