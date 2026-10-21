/-ai
The lift of a composite of approximable maps equals the composite of the lifts.

By extensionality, a master step of the lifted composite factors through the intermediate master, and a proper step factors through the intermediate false tag. In the other direction, passage through the intermediate master yields a master relation, while a second step from that master to a tag would put the empty string in a tag. Passage through a false tag yields a master relation when the second map sends that tag to the master, and yields a proper step of the composite when both steps are proper and the tags agree.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D : NeighborhoodSystem Str}


variable {hD : ∀ X, D.mem X → X.Nonempty}


variable {A B C : ScottSys}


/-- **`(g ∘ f)_⊥ = g_⊥ ∘ f_⊥`.** -/
theorem liftMapTok_comp (f : ApproximableMap A.sys B.sys) (g : ApproximableMap B.sys C.sys) :
    liftMapTok (g.comp f) = (liftMapTok g).comp (liftMapTok f) := by
  apply ApproximableMap.ext
  intro W W''
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X'', ⟨X', hf, hg⟩, rfl, rfl⟩)
    · exact ⟨liftTokMaster B.sys, Or.inl ⟨hW, rfl⟩,
        Or.inl ⟨(ScottSys.lift B).sys.master_mem, rfl⟩⟩
    · exact ⟨embBit false X', Or.inr ⟨X, X', hf, rfl, rfl⟩, Or.inr ⟨X', X'', hg, rfl, rfl⟩⟩
  · rintro ⟨W', hWW', hW'W''⟩
    rcases hWW' with ⟨hW, rfl⟩ | ⟨X, X', hf, rfl, rfl⟩
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X, X', -, heq, -⟩
      · exact Or.inl ⟨hW, rfl⟩
      · exact absurd (heq ▸ nil_mem_liftTokMaster) nil_not_mem_embBit
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X₂, X'', hg, heq, rfl⟩
      · exact Or.inl ⟨liftTok_mem_embF (hD := A.ne) (f.rel_dom hf), rfl⟩
      · obtain rfl := embBit_injective heq
        exact Or.inr ⟨X, X'', ⟨X', hf, hg⟩, rfl, rfl⟩

end Exercise619
end DomainTheory.NeighbourhoodSystems
