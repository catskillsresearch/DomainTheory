/-ai
The second projection relates neighbourhoods W and Z exactly when both belong to the sharp domain and either Z is the master neighbourhood or W is a paired embedding whose right-hand neighbourhood is contained in Z.

The two sides are definitionally equal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717.proj1Map

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)

@[simp] theorem proj1Map_rel {W Z : Set (List Bool × α)} :
    (proj1Map hD).rel W Z ↔
      MemS D W ∧ MemS D Z ∧ (Z = Gamma D ∨ ∃ Pp Qq, W = embPair Pp Qq ∧ Qq ⊆ Z) := Iff.rfl

end Proposition77

end DomainTheory.NeighbourhoodSystems
