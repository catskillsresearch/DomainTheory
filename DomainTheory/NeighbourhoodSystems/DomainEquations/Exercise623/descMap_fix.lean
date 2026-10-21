/-ai
The evaluation map satisfies the fixed-point equation: it equals the structure map composed with T of itself composed with the inverse structure map. Forward, an iterate lies, after one step of the recursion, under the structure map composed with T of the previous iterate composed with the inverse, and continuity on maps places that functor image under T of the union. Backward, a witness factoring through T of some iterate lands in the next iterate.

Continuity of the expression on the directed iterates, using that the evaluation map is their relational union, identifies pairs related by T of the evaluation map with pairs related by T of some iterate. Extensionality and the relational form of composition give both directions, using the successor inequality and the successor clause of the iterates.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gGen_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.mem_gColim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gColim_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.ext
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.Texp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.BasicInst28
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.id_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.comp_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFunctor_obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFunctorMap_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.algStr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.expInv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descRel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descRel_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descRel_le_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descDirLe
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descMap_is_sup
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.TexpF

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))

/-- **The fixed-point equation `val = k ∘ T(val) ∘ j`.** Forward: an iterate `valₙ` is, after the
recursion, `k ∘ T(valₙ₋₁) ∘ j`, and `T(valₙ₋₁) ⊆ T(val)` by continuity on maps. Backward: a witness
factoring through `T(valₙ)` lands in `valₙ₊₁`. -/
theorem descMap_fix :
    descMap hN B = (algStr B).comp (((Texp N).map (descMap hN B)).comp (expInv N hN)) := by
  have hmc : ∀ Y C, ((Texp N).map (descMap hN B)).rel Y C
      ↔ ∃ n, ((Texp N).map (descRel hN B n)).rel Y C :=
    fun Y C => (Texp N).map_continuous (descRel hN B) (descMap hN B) (descDirLe hN B)
      (descMap_is_sup hN B) Y C
  apply ApproximableMap.ext
  intro A E
  rw [comp_rel]
  constructor
  · rintro ⟨n, hn⟩
    have hn1 : (descRel hN B (n + 1)).rel A E := descRel_le_succ hN B n A E hn
    rw [descRel_succ, comp_rel] at hn1
    obtain ⟨C, hAC, hCE⟩ := hn1
    rw [comp_rel] at hAC
    obtain ⟨Y, hAY, hYC⟩ := hAC
    exact ⟨C, ⟨Y, hAY, (hmc Y C).mpr ⟨n, hYC⟩⟩, hCE⟩
  · rintro ⟨C, hAC, hCE⟩
    rw [comp_rel] at hAC
    obtain ⟨Y, hAY, hYC⟩ := hAC
    obtain ⟨n, hn⟩ := (hmc Y C).mp hYC
    refine ⟨n + 1, ?_⟩
    rw [descRel_succ, comp_rel]
    exact ⟨C, by rw [comp_rel]; exact ⟨Y, hAY, hn⟩, hCE⟩

end Existence

end Exercise619

end DomainTheory.NeighbourhoodSystems
