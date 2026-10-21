/-ai
The approximable map into the Sierpinski domain associated with a set U of elements relates a neighbourhood X to a Sierpinski neighbourhood Y when X is a neighbourhood and either Y is the whole token set or Y is empty and the basic open of X is contained in U. As an elementwise map it sends an element to the top precisely when that element lies in U. The codomain law is the two neighbourhoods of the Sierpinski system, and the master output is the whole token set. Right intersection is checked by cases on the two disjuncts. In the empty-output case of monotonicity, the whole-token alternative is excluded by the inclusion of outputs, and a smaller input has a smaller basic open.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.sierpinski

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise325

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {α : Type*} (V : NeighborhoodSystem α)

/-- `mapOfOpen U : 𝒟 → 𝒪`. It always relates `X` to the blunt neighbourhood `univ` of `𝒪`, and
relates `X` to the sharp neighbourhood `∅` exactly when the basic open `[X]` lies inside `U`. As an
elementwise map it sends `x` to `⊤` iff `x ∈ U`. -/
def mapOfOpen (U : Set V.Element) : ApproximableMap V sierpinski where
  rel X Y := V.mem X ∧ (Y = Set.univ ∨ (Y = ∅ ∧ V.basicOpen X ⊆ U))
  rel_dom h := h.1
  rel_cod h := by
    rcases h.2 with rfl | ⟨rfl, _⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  master_rel := ⟨V.master_mem, Or.inl rfl⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY⟩ ⟨_, hY'⟩
    refine ⟨hX, ?_⟩
    rcases hY with rfl | ⟨rfl, hsub⟩
    · rcases hY' with rfl | ⟨rfl, hsub'⟩
      · left; rw [Set.univ_inter]
      · right; rw [Set.univ_inter]; exact ⟨rfl, hsub'⟩
    · rcases hY' with rfl | ⟨rfl, _⟩
      · right; rw [Set.inter_univ]; exact ⟨rfl, hsub⟩
      · right; rw [Set.inter_self]; exact ⟨rfl, hsub⟩
  mono := by
    rintro X X' Y Y' ⟨hX, hY⟩ hX'X hYY' hX' hY'
    refine ⟨hX', ?_⟩
    rcases hY' with rfl | rfl
    · left; rfl
    · right
      refine ⟨rfl, ?_⟩
      rcases hY with rfl | ⟨rfl, hsub⟩
      · exact absurd (hYY' (Set.mem_univ ())) (by simp)
      · have hbo : V.basicOpen X' ⊆ V.basicOpen X := fun z hz => z.up_mem hz hX hX'X
        exact subset_trans hbo hsub

end DomainTheory.NeighbourhoodSystems.Exercise325
