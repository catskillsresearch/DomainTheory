/-ai
The approximable sharp injection acts on an element by Scott's map sending that element to its sharp image.

A sharp neighbourhood lies in the image when some neighbourhood of the element has its zero-embedding contained in it. The master neighbourhood of the sharp system arises immediately. A zero-embedding of a neighbourhood Y arises because the zero-embedding inclusion supplies the inclusion needed to place Y in the element. A pair neighbourhood cannot arise: some token of the domain neighbourhood has empty tag in the zero-embedding, that tagged token would have to lie in one component of the pair, and simplifying that membership is contradictory. Conversely, the master neighbourhood is witnessed by the master neighbourhood of D, and a zero-embedding of a neighbourhood of the element is witnessed by that neighbourhood itself.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)


/-- **`inSharpMap` really computes `inSharp`.** Its elementwise action is Scott's `λx. x^§`. -/
theorem inSharpMap_toElementMap (x : D.Element) :
    (inSharpMap hD).toElementMap x = inSharp D hD x := by
  apply Element.ext
  intro W
  simp only [ApproximableMap.mem_toElementMap, inSharpMap_rel]
  constructor
  · rintro ⟨X, hXx, hX, hW, hsub⟩
    cases hW with
    | gamma => exact Or.inl rfl
    | @zero Y hY => exact Or.inr ⟨Y, x.up_mem hXx hY (embZero_subset.mp hsub), rfl⟩
    | @pair Pp Qq hP hQ =>
      exfalso
      obtain ⟨a, ha⟩ := hD X hX
      rcases hsub (show (([], a) : List Bool × α) ∈ embZero X from ⟨rfl, ha⟩) with
        ⟨p', hp', -⟩ | ⟨q', hq', -⟩
      · simp at hp'
      · simp at hq'
  · rintro (rfl | ⟨Y, hYx, rfl⟩)
    · exact ⟨D.master, x.master_mem, D.master_mem, MemS.gamma, embZero_subset_Gamma D.master_mem⟩
    · exact ⟨Y, hYx, x.sub hYx, MemS.zero (x.sub hYx), subset_rfl⟩

end Proposition77
end DomainTheory.NeighbourhoodSystems
