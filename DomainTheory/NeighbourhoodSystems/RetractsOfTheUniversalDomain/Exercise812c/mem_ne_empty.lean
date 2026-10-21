/-ai
A neighbourhood of a system with no minimal neighbourhood is nonempty.

If the neighbourhood were empty, the absence of a minimal neighbourhood would supply a nonempty piece contained in a union equal to the empty set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.NoMinimal

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **`NoMinimal` forces `¬ D.mem ∅`, hence every genuine `D`-neighbourhood is non-empty.**
Applying `NoMinimal` at `X := ∅` would demand a non-empty `Y ⊆ Y ∪ Z = ∅`, impossible. (Exercise
8.12(c)(vi)(7): the one fact needed to know `hXmem`/`hYmem`'s enumerated sets are never `∅`, hence
— via the emptiness-transfer already proved in (5)(d) — that their `atomPair`-images `XPseq`/`YPseq`
are never `∅` either, i.e. always *genuine* neighbourhoods on the other side, no extra "extension"
hypothesis needed.) -/
theorem NeighborhoodSystem.NoMinimal.mem_ne_empty {α : Type*} {D : NeighborhoodSystem α}
    (hD : D.NoMinimal) {X : Set α} (hX : D.mem X) : X ≠ ∅ := by
  intro hXe
  subst hXe
  obtain ⟨Y, Z, -, -, hYne, -, -, hunion⟩ := hD hX
  exact hYne.ne_empty (Set.union_empty_iff.mp hunion).1

end DomainTheory.NeighbourhoodSystems
