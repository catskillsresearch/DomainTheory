/-ai
The coalesced sum carries the subsystem relation componentwise.

The masters agree by unfolding the sum master and rewriting the two component masters. Membership sends the master to the master, and a proper tag along the corresponding subsystem, rewriting properness by the component master equality. For intersections, two masters remain the master, and a master meeting a tag reduces by the intersection of the sum master with that tag, commuting when the tag comes first. Two false tags intersect by the bit-embedding intersection; the left subsystem closes the component intersection after the inverse false-tag membership lemma, and properness is the left-factor intersection lemma. Opposite bits have empty intersection, which contradicts nonemptiness. Two true tags are symmetric, using the inverse true-tag membership lemma.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.oplusTok_mem_embF_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.oplusTok_mem_embT_inv

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}

/-- The coalesced sum carries the subsystem relation componentwise. -/
theorem oplusTok_subsystem (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    (A₀.oplus A₁).sys ◁ (B₀.oplus B₁).sys := by
  have heqm : sumTokMaster A₀.sys A₁.sys = sumTokMaster B₀.sys B₁.sys := by
    unfold sumTokMaster; rw [h0.master_eq, h1.master_eq]
  refine ⟨heqm, ?_, ?_⟩
  · rintro W (rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩)
    · exact Or.inl heqm
    · exact Or.inr (Or.inl ⟨X, h0.sub hX, h0.master_eq ▸ hXne, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, h1.sub hY, h1.master_eq ▸ hYne, rfl⟩)
  · rintro W W' (rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩)
      (rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩) hInt
    · rw [Set.inter_self]; exact Or.inl rfl
    · rw [sumTokMaster_inter_embF hX']; exact Or.inr (Or.inl ⟨X', hX', hX'ne, rfl⟩)
    · rw [sumTokMaster_inter_embT hY']; exact Or.inr (Or.inr ⟨Y', hY', hY'ne, rfl⟩)
    · rw [Set.inter_comm, sumTokMaster_inter_embF hX]; exact Or.inr (Or.inl ⟨X, hX, hXne, rfl⟩)
    · rw [embBit_inter] at hInt ⊢
      exact Or.inr (Or.inl ⟨X ∩ X',
        h0.inter_closed hX hX' (oplusTok_mem_embF_inv (h₀ := B₀.ne) (h₁ := B₁.ne) hInt),
        inter_ne_of_ne_left (A₀.sys.sub_master hX) hXne, rfl⟩)
    · rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hInt
      exact absurd ((B₀.oplus B₁).ne _ hInt) Set.not_nonempty_empty
    · rw [Set.inter_comm, sumTokMaster_inter_embT hY]; exact Or.inr (Or.inr ⟨Y, hY, hYne, rfl⟩)
    · rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hInt
      exact absurd ((B₀.oplus B₁).ne _ hInt) Set.not_nonempty_empty
    · rw [embBit_inter] at hInt ⊢
      exact Or.inr (Or.inr ⟨Y ∩ Y',
        h1.inter_closed hY hY' (oplusTok_mem_embT_inv (h₀ := B₀.ne) (h₁ := B₁.ne) hInt),
        inter_ne_of_ne_left (A₁.sys.sub_master hY) hYne, rfl⟩)

end Exercise619
end DomainTheory.NeighbourhoodSystems
