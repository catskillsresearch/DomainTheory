module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}




section Algebraic

variable {γ : Type u} {V : NeighborhoodSystem γ}






/-- **Compact elements are principal** — the converse of `principal_isCompactElt`, via
algebraicity: test compactness against `x`'s own principal-approximant family. -/
theorem eq_principal_of_isCompactElt {x : V.Element} (hx : IsCompactElt x) :
    ∃ (X : Set γ) (hX : V.mem X), x = V.principal hX := by
  have hle : x ≤ iSupDirected (fun i : {X : Set γ // x.mem X} => V.principal (x.sub i.2))
      (principalFamily_directed x) := le_of_eq (eq_iSupDirected_principal x)
  obtain ⟨i0, hi0⟩ :=
    hx (fun i : {X : Set γ // x.mem X} => V.principal (x.sub i.2)) (principalFamily_directed x) hle
  exact ⟨i0.1, x.sub i0.2, le_antisymm hi0 (principal_le_of_mem i0.2)⟩

end Algebraic
end DomainTheory.NeighbourhoodSystems
