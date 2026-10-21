/-ai
The set represented by the union of two elements is the union of the sets they represent.

A number whose singleton complement belongs to the union comes from input neighbourhoods whose intersection is contained in that singleton complement. If the number lies in the first neighbourhood, it is absent from the second and the second element contains the singleton complement; otherwise the first element contains it. If the number lies in the first represented set, the singleton complement and the universe witness the relation, and if it lies in the second represented set, the universe and the singleton complement do.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem
























theorem toSet_unionMap (x y : powerSet.Element) :
    toSet (unionMap.toElementMap₂ x y) = toSet x ∪ toSet y := by
  ext k
  simp only [mem_toSet, ApproximableMap₂.mem_toElementMap₂, Set.mem_union]
  constructor
  · rintro ⟨X, Y, hxX, hyY, _, _, _, hsub⟩
    by_cases hkX : k ∈ X
    · refine Or.inr ?_
      have hkY : k ∉ Y := fun hkY => (hsub ⟨hkX, hkY⟩) rfl
      exact y.up_mem hyY (mem_compl_singleton k) (Set.subset_compl_singleton_iff.mpr hkY)
    · exact Or.inl (x.up_mem hxX (mem_compl_singleton k) (Set.subset_compl_singleton_iff.mpr hkX))
  · rintro (hkx | hky)
    · exact ⟨{k}ᶜ, Set.univ, hkx, y.master_mem, mem_compl_singleton k, powerSet.master_mem,
        mem_compl_singleton k, Set.inter_subset_left⟩
    · exact ⟨Set.univ, {k}ᶜ, x.master_mem, hky, powerSet.master_mem, mem_compl_singleton k,
        mem_compl_singleton k, Set.inter_subset_right⟩

end DomainTheory.NeighbourhoodSystems.Exercise220
