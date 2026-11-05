module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.iInter
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.iUnion

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem

/-- Scott's Theorem 1.11: countable intersections of ideal elements, and directed
(monotone) countable unions, are again ideal elements — characterized by
pointwise membership. -/
theorem theorem_111 :
    (∀ {α : Type*} (V : NeighborhoodSystem α) (x : ℕ → V.Element) {X : Set α},
      (V.iInter x).mem X ↔ ∀ n, (x n).mem X) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α) (x : ℕ → V.Element) (hmono : Monotone x)
      {X : Set α}, (V.iUnion x hmono).mem X ↔ ∃ n, (x n).mem X) :=
  ⟨mem_iInter, mem_iUnion⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
