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
