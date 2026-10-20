module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Iter.mapOfSeq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Iter.exists_forall_swap

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The value of `mapOfSeq g` is the sequence of values `⟨gᵢ(x)⟩`. -/
theorem toElementMap_mapOfSeq (g : ℕ → ApproximableMap V₀ V₁) (x : V₀.Element) :
    (mapOfSeq g).toElementMap x = ofSeq (fun i => (g i).toElementMap x) := by
  apply Element.ext
  intro W
  constructor
  · rintro ⟨X, hXx, _, hW, hrel⟩
    exact ⟨hW, fun i => ⟨X, hXx, hrel i⟩⟩
  · rintro ⟨hW, hfib⟩
    obtain ⟨X, hXx, hrel⟩ := (exists_forall_swap hW).mpr (fun i => hfib i)
    exact ⟨X, hXx, x.sub hXx, hW, hrel⟩

end DomainTheory.NeighbourhoodSystems
