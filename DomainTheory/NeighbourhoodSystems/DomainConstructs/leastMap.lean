module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.interYs

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

def leastMap (L : List (Set α × Set β)) (_hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) : ApproximableMap V₀ V₁ where
  rel X Y := V₀.mem X ∧ V₁.mem Y ∧ interYs V₁.master L X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V₀.master_mem, V₁.master_mem, interYs_subset_master⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hsub⟩ ⟨_, hY', hsub'⟩
    exact ⟨hX, V₁.inter_mem hY hY' (hcons hX) (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hsub⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', (interYs_antitone hX'X).trans (hsub.trans hYY')⟩

@[simp] theorem leastMap_rel {L : List (Set α × Set β)}
    {hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2}
    {hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)} {X : Set α} {Y : Set β} :
    (leastMap L hL hcons).rel X Y ↔ V₀.mem X ∧ V₁.mem Y ∧ interYs V₁.master L X ⊆ Y := Iff.rfl

end DomainTheory.NeighbourhoodSystems
