/-ai
The neighbourhood system on binary words takes membership to be Scott's family, and takes the master neighbourhood to be the set of all words. The master neighbourhood is nonempty and belongs to the family, the intersection law is the intersection law of the family, and every member is contained in the master neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.InS
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.mem_concat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Ssys_master_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Ssys_master_nonempty
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Ssys_sub_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Ssys_inter_mem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open NeighborhoodSystem ApproximableMap

/-- **Exercise 7.22 (neighbourhood-system part).** `S` is a *positive* neighbourhood system over the
token type `Σ = {0,1}*`, with master neighbourhood `Δ = Σ = Set.univ`. Proof fields are named so
Palomar can lock this value. -/
def Ssys : NeighborhoodSystem (List Bool) where
  mem := InS
  master := Set.univ
  master_nonempty := Ssys_master_nonempty
  master_mem := Ssys_master_mem
  inter_mem := Ssys_inter_mem
  sub_master := Ssys_sub_master

end Exercise722

end DomainTheory.NeighbourhoodSystems
