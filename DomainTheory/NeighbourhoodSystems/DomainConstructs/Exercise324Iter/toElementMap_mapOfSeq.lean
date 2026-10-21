/-ai
The value of an infinite pairing at an element is the sequence of the values of the component maps at that element.

A neighbourhood of the paired value comes from an input neighbourhood related on every fibre, which is membership of each fibre in the corresponding value. Conversely, membership of every fibre gives an input neighbourhood at each coordinate, and one neighbourhood that works for all coordinates is obtained by swapping the quantifiers.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Iter.mapOfSeq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Iter.exists_forall_swap

@[expose] public section

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
