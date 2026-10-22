module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Data.Set.Finite.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_toSet

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Filters are determined on cofinite sets by their singleton-complements.** For cofinite `Z`,
`Z ∈ x ↔ ∀ n ∈ Zᶜ, {n}ᶜ ∈ x` (since `Z = ⋂_{n ∈ Zᶜ} {n}ᶜ`, a *finite* intersection). -/
theorem mem_compl_of_finite (x : powerSet.Element) {t : Set ℕ} (ht : t.Finite)
    (h : ∀ n ∈ t, x.mem ({n}ᶜ)) : x.mem (tᶜ) := by
  revert h
  induction t, ht using Set.Finite.induction_on with
  | empty => intro _; rw [Set.compl_empty]; exact x.master_mem
  | @insert a s _ha _hsfin ih =>
    intro h
    have hcompl : (insert a s)ᶜ = ({a}ᶜ) ∩ (sᶜ) := by rw [Set.insert_eq, Set.compl_union]
    rw [hcompl]
    exact x.inter_mem (h a (Set.mem_insert a s))
      (ih (fun n hn => h n (Set.mem_insert_of_mem a hn)))

end DomainTheory.NeighbourhoodSystems.Exercise220
