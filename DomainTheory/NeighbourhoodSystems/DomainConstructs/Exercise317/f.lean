module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.T
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.encSet
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.mem_encSet
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.encSet_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.encSet_mem
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.encSet_anti

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- **The encoding map `f : B → T^∞`.** Relates the cone `σΣ*` to every `T^∞`-neighbourhood weaker
than `encSet σ`. -/
def f : ApproximableMap B (iterSys T) where
  rel X W := ∃ σ, X = cone σ ∧ (iterSys T).mem W ∧ encSet σ ⊆ W
  rel_dom := fun ⟨σ, hX, _⟩ => hX ▸ memB_cone σ
  rel_cod := fun ⟨_, _, hW, _⟩ => hW
  master_rel := ⟨[], cone_nil.symm, (iterSys T).master_mem, by rw [encSet_nil]; exact Set.subset_univ _⟩
  inter_right := by
    rintro X W W' ⟨σ, hX, hWmem, hWsub⟩ ⟨σ', hX', hW'mem, hW'sub⟩
    obtain rfl : σ = σ' := cone_injective (hX.symm.trans hX')
    exact ⟨σ, hX, (iterSys T).inter_mem hWmem hW'mem (encSet_mem σ)
      (Set.subset_inter hWsub hW'sub), Set.subset_inter hWsub hW'sub⟩
  mono := by
    rintro X X' W W' ⟨σ, hX, _, hWsub⟩ hX'X hWW' hX' hW'mem
    obtain ⟨σ', rfl⟩ := hX'
    subst hX
    have hpre : σ <+: σ' := cone_subset_cone.mp hX'X
    exact ⟨σ', rfl, hW'mem, (encSet_anti hpre).trans (hWsub.trans hWW')⟩

end DomainTheory.NeighbourhoodSystems.Exercise317
