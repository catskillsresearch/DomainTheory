/-ai
The flat two-point neighbourhood system on the booleans has as neighbourhoods the full set and the two singletons of true and of false, with master neighbourhood the full set. The master neighbourhood is nonempty and is a neighbourhood, and every neighbourhood is contained in it. Whenever a neighbourhood is contained in an intersection of two neighbourhoods, that intersection is a neighbourhood: every neighbourhood is nonempty, the intersection of the two distinct singletons is empty, and in every other case the intersection equals the full set or one of the two singletons.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.PDsingletonApproxMap_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.PDsingletonMeet_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.finJoinMap_prod_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.tf_inter
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.ft_inter

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace Counterexample712C

open NeighborhoodSystem

variable {γ δ : Type*}

/-- The flat two-point domain over `Bool`: the neighbourhoods are the master `Δ = {true, false}`
and the two singletons `{true}`, `{false}`. Since `{true} ∩ {false} = ∅` and `∅` is not a
neighbourhood (and has no neighbourhood subset), condition (ii) holds only vacuously there — this is
a genuine Scott neighbourhood system whose two singletons are *inconsistent*. -/
def Vshape : NeighborhoodSystem Bool where
  mem X := X = Set.univ ∨ X = {true} ∨ X = {false}
  master := Set.univ
  master_nonempty := ⟨true, Set.mem_univ _⟩
  master_mem := Or.inl rfl
  sub_master _ := Set.subset_univ _
  inter_mem := by
    rintro X Y Z hX hY hZ hZsub
    -- every neighbourhood is nonempty, so a witness `Z ⊆ X ∩ Y = ∅` is impossible
    have hZne : Z.Nonempty := by
      rcases hZ with rfl | rfl | rfl
      · exact ⟨true, Set.mem_univ true⟩
      · exact ⟨true, rfl⟩
      · exact ⟨false, rfl⟩
    obtain ⟨z, hz⟩ := hZne
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl (by rw [Set.univ_inter]))
    · exact Or.inr (Or.inr (by rw [Set.univ_inter]))
    · exact Or.inr (Or.inl (by rw [Set.inter_univ]))
    · exact Or.inr (Or.inl (by rw [Set.inter_self]))
    · rw [tf_inter] at hZsub; exact absurd (hZsub hz) (Set.notMem_empty z)
    · exact Or.inr (Or.inr (by rw [Set.inter_univ]))
    · rw [ft_inter] at hZsub; exact absurd (hZsub hz) (Set.notMem_empty z)
    · exact Or.inr (Or.inr (by rw [Set.inter_self]))

end Counterexample712C

end DomainTheory.NeighbourhoodSystems
