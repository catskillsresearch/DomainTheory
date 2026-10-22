module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.MemS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embZero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embL
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embR
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_Gamma

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem embPair_subset {P Q P' Q' : Set (List Bool × α)} :
    embPair P Q ⊆ embPair P' Q' ↔ P ⊆ P' ∧ Q ⊆ Q' := by
  constructor
  · intro h
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · obtain ⟨p', a⟩ := t
      have hmem : ((true :: p', a) : List Bool × α) ∈ embPair P' Q' :=
        h (Or.inl ⟨p', rfl, ht⟩)
      rcases hmem with ⟨p'', hp'', hP'⟩ | ⟨q'', hq'', -⟩
      · simp only [List.cons.injEq, true_and] at hp''; exact hp'' ▸ hP'
      · exact absurd hq'' (by simp)
    · obtain ⟨q', a⟩ := t
      have hmem : ((false :: q', a) : List Bool × α) ∈ embPair P' Q' :=
        h (Or.inr ⟨q', rfl, ht⟩)
      rcases hmem with ⟨p'', hp'', -⟩ | ⟨q'', hq'', hQ'⟩
      · exact absurd hp'' (by simp)
      · simp only [List.cons.injEq, true_and] at hq''; exact hq'' ▸ hQ'
  · rintro ⟨hP, hQ⟩ t ht
    rcases ht with ⟨p', hp', hPmem⟩ | ⟨q', hq', hQmem⟩
    · exact Or.inl ⟨p', hp', hP hPmem⟩
    · exact Or.inr ⟨q', hq', hQ hQmem⟩

end Example61

end DomainTheory.NeighbourhoodSystems
