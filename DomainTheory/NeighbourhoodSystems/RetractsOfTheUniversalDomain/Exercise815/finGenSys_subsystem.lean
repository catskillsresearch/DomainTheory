/-ai
The finitely generated subsystem on a list is a subsystem of the original neighbourhood system.

The masters agree. Every member is a neighbourhood of the original system. The intersection of two members is the partial meet of the combined sub-selection, and that partial meet equals the intersection of the two partial meets.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen_sub_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.combineSub
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.combineSub_sublist
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.interFrom_combineSub_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGenSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_finGenSys

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section FinGen

variable (P : ComputablePresentation D)

/-- **`Fin(js)` is a subsystem of `D`** (Definition 6.10). -/
theorem finGenSys_subsystem (js : List ℕ) : finGenSys P js ◁ D where
  master_eq := rfl
  sub := finGen_sub_mem P
  inter_closed := by
    rintro X Y ⟨sub1, h1, hDX, hX⟩ ⟨sub2, h2, hDY, hY⟩ hXY
    exact ⟨combineSub js sub1 sub2, combineSub_sublist js sub1 sub2, hXY, by
      rw [interFrom_combineSub_eq P h1 h2, hX, hY]⟩

end FinGen

end DomainTheory.NeighbourhoodSystems
