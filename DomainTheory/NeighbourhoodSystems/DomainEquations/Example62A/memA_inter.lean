/-ai
For positive n, the family MemA is closed under consistent intersection: if X, Y, and Z belong to MemA and Z is contained in the intersection of X and Y, then that intersection belongs to MemA.

Induction on the membership of X. When X is the set of all strings, the intersection is Y. When X is a tagged tuple and Y is the set of all strings, the intersection is that tuple. When both are tagged tuples of the same tag, the intersection law rewrites the inclusion; the consistency neighbourhood cannot be the set of all strings, because the empty string would then lie in the tuple, and when it is a tuple the tag lemma and the subset lemma give componentwise inclusions to which the inductive hypothesis applies. When the tags differ, the intersection is empty, which cannot contain a nonempty witness from Z.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.MemA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.npow_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_embTuple
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.nil_not_mem_embTuple
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_inter_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.memA_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.tag_eq_of_subset

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

variable {n : ℕ}

/-- **`A` is closed under consistent intersection.** Scott's verification, by induction on the way `X`
entered `A`: the cross case `embTuple false · ∩ embTuple true ·` collapses to `∅` (killed by the
non-empty witness), the same-tag case combines componentwise (recursing on the consistency witness's
slots). -/
theorem memA_inter (hn : 0 < n) :
    ∀ {X}, MemA n X → ∀ {Y}, MemA n Y → ∀ {Z}, MemA n Z → Z ⊆ X ∩ Y → MemA n (X ∩ Y) := by
  intro X hX
  induction hX with
  | univ =>
    intro Y hY Z _ _
    rw [Set.univ_inter]; exact hY
  | @tuple i X hX ih =>
    intro Y hY Z hZ hsub
    cases hY with
    | univ =>
      rw [Set.inter_univ]; exact MemA.tuple i hX
    | @tuple i' X' hX' =>
      by_cases hii : i = i'
      · rw [hii, embTuple_inter] at hsub ⊢
        cases hZ with
        | univ => exact absurd (hsub (Set.mem_univ [])) nil_not_mem_embTuple
        | @tuple i'' ZW hZW =>
          have htag : i'' = i' := tag_eq_of_subset hn hZW hsub
          rw [htag] at hsub
          have hZsub := embTuple_subset.mp hsub
          exact MemA.tuple i' (fun j => ih j (hX' j) (hZW j) (hZsub j))
      · rw [embTuple_inter_ne hii] at hsub ⊢
        exfalso
        obtain ⟨z, hz⟩ := memA_nonempty hn hZ
        exact Set.notMem_empty z (hsub hz)

end Example62A

end DomainTheory.NeighbourhoodSystems
