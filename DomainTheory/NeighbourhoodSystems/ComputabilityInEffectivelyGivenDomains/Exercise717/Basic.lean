module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717.proj1Map
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717.pairSharpMap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717.proj1Map_rel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)


@[simp] theorem pairSharpMap_rel {V : Set ((List Bool × α) ⊕ (List Bool × α))}
    {W : Set (List Bool × α)} :
    (pairSharpMap hD).rel V W ↔
      (prod (Dsharp D hD) (Dsharp D hD)).mem V ∧ MemS D W ∧
        ∃ A B, MemS D A ∧ MemS D B ∧ V = prodNbhd A B ∧ embPair A B ⊆ W := Iff.rfl
end Proposition77
end DomainTheory.NeighbourhoodSystems
