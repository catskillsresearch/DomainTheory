/-ai
If F is a finite set of natural numbers and the complement of every singleton of a point of F lies in a cofinite filter, then the complement of F lies in the filter.

The proof inducts on the finite set. For the empty set, the complement is the whole set of natural numbers, which is the master neighbourhood. When a point is inserted into a finite set, the complement of the union is the intersection of the complements, and the filter contains that intersection because it contains the complement of the inserted singleton and, by the inductive hypothesis, the complement of the remaining set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.cofiniteSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.cofiniteSystem_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.mem_ofExcluded
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.mem_toExcluded

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem

/-- **Reconstruction lemma.** For finite `F` of points each of whose single-deletion `{n}ᶜ`
is in the filter `x`, the intersection `⋂_{n∈F} {n}ᶜ = Fᶜ` is also in `x`. -/
theorem mem_compl_of_finite (x : cofiniteSystem.Element) {F : Set ℕ} (hF : F.Finite) :
    (∀ n ∈ F, x.mem ({n}ᶜ)) → x.mem (Fᶜ) := by
  induction F, hF using Set.Finite.induction_on with
  | empty => intro _; rw [Set.compl_empty]; exact x.master_mem
  | @insert a s _ _ ih =>
    intro h
    rw [Set.insert_eq, Set.compl_union]
    exact x.inter_mem (h a (Set.mem_insert a s))
      (ih (fun n hn => h n (Set.mem_insert_of_mem a hn)))

end Cofinite

end DomainTheory.NeighbourhoodSystems
