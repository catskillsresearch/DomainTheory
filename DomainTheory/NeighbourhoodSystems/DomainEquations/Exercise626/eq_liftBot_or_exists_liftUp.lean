module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftUp_unlift

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D : NeighborhoodSystem Str}


variable {hD : ∀ X, D.mem X → X.Nonempty}


/-- **Exercise 6.26 — "describe in terms of elements".** Every element of `𝒟_⊥` is either the fresh
bottom or a lifted `𝒟`-element: `|𝒟_⊥| ≅ |𝒟|_⊥`. (`Prop`-level; the case split on "does `z` contain
`0Δ`?" uses excluded middle — the only non-constructive step in this module.) -/
theorem eq_liftBot_or_exists_liftUp (z : (liftTok D hD).Element) :
    z = liftBot D hD ∨ ∃ x : D.Element, z = liftUp (hD := hD) x := by
  by_cases hz : z.mem (embBit false D.master)
  · exact Or.inr ⟨unlift z hz, (liftUp_unlift z hz).symm⟩
  · refine Or.inl ?_
    apply NeighborhoodSystem.Element.ext
    intro W
    constructor
    · intro hW
      rcases z.sub hW with rfl | ⟨X, hX, rfl⟩
      · rfl
      · exact absurd
          (z.up_mem hW (liftTok_mem_embF D.master_mem) (embBit_subset.mpr (D.sub_master hX))) hz
    · rintro rfl; exact z.master_mem

end Exercise619
end DomainTheory.NeighbourhoodSystems
