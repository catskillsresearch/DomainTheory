module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.nil_mem_liftTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTokMaster_inter_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.lift
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTok_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.mem_liftBot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.mem_liftUp

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

/-- **`f_⊥`, the action of lifting on (approximable) maps.** It carries the master to the master (so
it is strict) and a copy `0X` to `0X'` whenever `X f X'`. -/
def liftMapTok (f : ApproximableMap A.sys B.sys) :
    ApproximableMap (ScottSys.lift A).sys (ScottSys.lift B).sys where
  rel W W' :=
    ((liftTok A.sys A.ne).mem W ∧ W' = liftTokMaster B.sys) ∨
    (∃ X X', f.rel X X' ∧ W = embBit false X ∧ W' = embBit false X')
  rel_dom := by
    rintro W W' (⟨hW, -⟩ | ⟨X, X', hrel, rfl, -⟩)
    · exact hW
    · exact liftTok_mem_embF (hD := A.ne) (f.rel_dom hrel)
  rel_cod := by
    rintro W W' (⟨-, rfl⟩ | ⟨X, X', hrel, -, rfl⟩)
    · exact Or.inl rfl
    · exact liftTok_mem_embF (hD := B.ne) (f.rel_cod hrel)
  master_rel := Or.inl ⟨(ScottSys.lift A).sys.master_mem, rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ h1 h2
    rcases h1 with ⟨hW, rfl⟩ | ⟨X, X', hrel, rfl, rfl⟩
    · rcases h2 with ⟨-, rfl⟩ | ⟨X, X', hrel, hWeq, rfl⟩
      · exact Or.inl ⟨hW, by rw [Set.inter_self]⟩
      · exact Or.inr ⟨X, X', hrel, hWeq, by rw [liftTokMaster_inter_embF (f.rel_cod hrel)]⟩
    · rcases h2 with ⟨-, rfl⟩ | ⟨X₂, X'₂, hrel₂, hWeq, rfl⟩
      · refine Or.inr ⟨X, X', hrel, rfl, ?_⟩
        rw [Set.inter_comm, liftTokMaster_inter_embF (f.rel_cod hrel)]
      · obtain rfl := embBit_injective hWeq
        exact Or.inr ⟨X, X' ∩ X'₂, f.inter_right hrel hrel₂, rfl, embBit_inter false X' X'₂⟩
  mono := by
    rintro W W'' Z Z' h hWW hZZ' hZmem hZ'mem
    rcases h with ⟨-, rfl⟩ | ⟨X, X', hrel, rfl, rfl⟩
    · exact Or.inl ⟨hZmem, Set.Subset.antisymm ((ScottSys.lift B).sys.sub_master hZ'mem) hZZ'⟩
    · rcases hZ'mem with rfl | ⟨X₃, hX₃, rfl⟩
      · exact Or.inl ⟨hZmem, rfl⟩
      · rcases hZmem with rfl | ⟨X₂, hX₂, rfl⟩
        · exact absurd (hWW nil_mem_liftTokMaster) nil_not_mem_embBit
        · exact Or.inr ⟨X₂, X₃,
            f.mono hrel (embBit_subset.mp hWW) (embBit_subset.mp hZZ') hX₂ hX₃, rfl, rfl⟩

end Exercise619

end DomainTheory.NeighbourhoodSystems
