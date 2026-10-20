module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.nil_mem_liftTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.embF_subset_liftTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTokMaster_inter_embF

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D : NeighborhoodSystem Str}

/-- **Exercise 6.26 — the lifted system `𝒟_⊥` over `{0,1}*`.** A neighbourhood is the master
`{Λ} ∪ 0Δ` or a tagged copy `0X` (`X ∈ 𝒟`). `∅`-freeness of `𝒟` (`hD`) keeps it `∅`-free. -/
def liftTok (D : NeighborhoodSystem Str) (_hD : ∀ X, D.mem X → X.Nonempty) :
    NeighborhoodSystem Str where
  mem W := W = liftTokMaster D ∨ ∃ X, D.mem X ∧ W = embBit false X
  master := liftTokMaster D
  master_nonempty := ⟨[], nil_mem_liftTokMaster⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨X, hX, rfl⟩)
    · exact subset_rfl
    · exact embF_subset_liftTokMaster hX
  inter_mem := by
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | ⟨X, hX, rfl⟩
    · rcases hW' with rfl | ⟨X', hX', rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [liftTokMaster_inter_embF hX']; exact Or.inr ⟨X', hX', rfl⟩
    · rcases hW' with rfl | ⟨X', hX', rfl⟩
      · rw [Set.inter_comm, liftTokMaster_inter_embF hX]; exact Or.inr ⟨X, hX, rfl⟩
      · rw [embBit_inter] at hZsub ⊢
        rcases hZ with rfl | ⟨Z', hZ', rfl⟩
        · exact absurd (hZsub nil_mem_liftTokMaster) nil_not_mem_embBit
        · exact Or.inr ⟨X ∩ X', D.inter_mem hX hX' hZ' (embBit_subset.mp hZsub), rfl⟩

end Exercise619

end DomainTheory.NeighbourhoodSystems
