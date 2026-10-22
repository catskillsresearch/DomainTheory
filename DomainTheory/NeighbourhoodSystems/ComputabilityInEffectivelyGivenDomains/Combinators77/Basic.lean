module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77.inSharpMap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77.proj0Map
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77.dsharpPresentation_X
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77.inSharpMap_rel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)


@[simp] theorem proj0Map_rel {W Z : Set (List Bool × α)} :
    (proj0Map hD).rel W Z ↔
      MemS D W ∧ MemS D Z ∧ (Z = Gamma D ∨ ∃ Pp Qq, W = embPair Pp Qq ∧ Pp ⊆ Z) := Iff.rfl
end Proposition77
end DomainTheory.NeighbourhoodSystems
