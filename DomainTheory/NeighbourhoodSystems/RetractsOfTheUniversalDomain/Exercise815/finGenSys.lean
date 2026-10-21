/-ai
The finitely generated subsystem on a list, regarded as a neighbourhood system, has the same master as the original system, and a set belongs to it precisely when it belongs to that finitely generated collection. The master belongs to the collection. The intersection of two members, when it contains a third member, is the partial meet of the combined sub-selection, which is still a sublist. Every member is contained in the master, because every partial meet is.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.master_mem_finGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.combineSub
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.combineSub_sublist
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.interFrom_combineSub_eq

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section FinGen

variable (P : ComputablePresentation D)

/-- **`Fin(js)` as a `NeighborhoodSystem`.** Master is `D.master`; closure under consistent
intersection combines the two witnessing sub-selections via `combineSub`. -/
def finGenSys (js : List ℕ) : NeighborhoodSystem α where
  mem Y := Y ∈ finGen P js
  master := D.master
  master_nonempty := D.master_nonempty
  master_mem := master_mem_finGen P js
  inter_mem := by
    rintro X Y Z ⟨sub1, h1, hDX, hX⟩ ⟨sub2, h2, hDY, hY⟩ ⟨sub3, h3, hDZ, hZ⟩ hZsub
    exact ⟨combineSub js sub1 sub2, combineSub_sublist js sub1 sub2,
      D.inter_mem hDX hDY hDZ hZsub, by
        rw [interFrom_combineSub_eq P h1 h2, hX, hY]⟩
  sub_master := fun ⟨sub, _, _, hY⟩ => hY ▸ interFrom_subset P

end FinGen

end DomainTheory.NeighbourhoodSystems
