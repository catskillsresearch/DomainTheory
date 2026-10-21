/-ai
The embedding of an element x of D into the lift is the element whose neighbourhoods are the lift master and the false-tagged copies of the neighbourhoods of x. Downward closure preserves each disjunct, and the master belongs by the left disjunct. The intersection of the master with itself is the master. The intersection of the master with a false-tagged neighbourhood reduces to that neighbourhood by the master-intersection law, and the intersection of two false-tagged neighbourhoods is the false tag of their intersection in x. A set above the master equals the master, because the master is the greatest neighbourhood of the lift. A set above a false-tagged neighbourhood is the master, or a larger false-tagged neighbourhood whose underlying set lies above the original neighbourhood in x.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTokMaster_inter_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTok

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

/-- The **embedding** `|𝒟| ↪ |𝒟_⊥|`: `liftUp x = {{Λ} ∪ 0Δ} ∪ {0X ∣ X ∈ x}`, the image of `x`
sitting above the fresh bottom. -/
def liftUp {D : NeighborhoodSystem Str} {hD : ∀ X, D.mem X → X.Nonempty} (x : D.Element) :
    (liftTok D hD).Element where
  mem W := W = liftTokMaster D ∨ ∃ X, x.mem X ∧ W = embBit false X
  sub := by
    rintro W (rfl | ⟨X, hX, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨X, x.sub hX, rfl⟩
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl⟩) (rfl | ⟨X', hX', rfl⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨X', hX', by rw [liftTokMaster_inter_embF (x.sub hX')]⟩
    · exact Or.inr ⟨X, hX, by rw [Set.inter_comm, liftTokMaster_inter_embF (x.sub hX)]⟩
    · exact Or.inr ⟨X ∩ X', x.inter_mem hX hX', by rw [embBit_inter]⟩
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm ((liftTok D hD).sub_master hW') hsub)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨X', x.up_mem hX hX' (embBit_subset.mp hsub), rfl⟩

end Exercise619

end DomainTheory.NeighbourhoodSystems
