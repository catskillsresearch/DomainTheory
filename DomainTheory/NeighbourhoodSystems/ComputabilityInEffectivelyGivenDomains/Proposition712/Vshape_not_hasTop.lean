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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.Vshape_mem_true
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.Vshape_mem_false
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.Vshape_not_mem_empty

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive



namespace Counterexample712C

open NeighborhoodSystem

variable {γ δ : Type*}







/-- **`|Vshape|` has no greatest element.** A greatest element would contain both `{true}` and
`{false}`, hence (by `inter_mem`) their intersection `∅`, which is not a neighbourhood. -/
theorem Vshape_not_hasTop : ¬ HasTop Vshape := by
  rintro ⟨t, ht⟩
  have htt : t.mem {true} :=
    ht (Vshape.principal Vshape_mem_true) {true} ⟨Vshape_mem_true, subset_rfl⟩
  have htf : t.mem {false} :=
    ht (Vshape.principal Vshape_mem_false) {false} ⟨Vshape_mem_false, subset_rfl⟩
  have hint : t.mem (({true} : Set Bool) ∩ {false}) := t.inter_mem htt htf
  rw [tf_inter] at hint
  exact Vshape_not_mem_empty (t.sub hint)

end Counterexample712C
end DomainTheory.NeighbourhoodSystems
