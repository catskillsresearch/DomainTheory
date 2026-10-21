/-ai
The singleton of a string lies in the inverse image of an element of D' if and only if the cone of that string's completed encoding lies in the element.

A cone clause would make a cone equal a singleton. A singleton clause has the same string because the string belongs to that singleton. In the other direction, membership of the completed cone is the singleton clause.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.encC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_cons
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.fromD'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.cone_ne_singleton
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.toD'_mem_enc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.toD'_mem_encC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.fromD'_mem_cone

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822

@[simp] theorem fromD'_mem_singleton {y : D'.Element} (κ : Str) :
    (fromD' y).mem ({κ} : Set Str) ↔ y.mem (cone (encC κ)) := by
  constructor
  · rintro (⟨σ, hσ, heq⟩ | ⟨σ, hσ, heq⟩)
    · exact absurd heq.symm (cone_ne_singleton σ κ)
    · have hκσ : κ = σ := by
        have h1 : κ ∈ ({σ} : Set Str) := heq ▸ rfl
        simpa using h1
      rw [hκσ]; exact hσ
  · intro hy; exact Or.inr ⟨κ, hy, rfl⟩

end Exercise822

end DomainTheory.NeighbourhoodSystems
