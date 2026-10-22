module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.StrictMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstep
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstepFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstepFun_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep_master_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun_mem_inter
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.toStrictMap_rel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **The filter `f̂ = {F ∣ f ∈ F}` of a strict map.** -/
def toStrictFilter (f : StrictMap V₀ V₁) : (strictFun V₀ V₁).Element where
  mem W := (strictFun V₀ V₁).mem W ∧ f ∈ W
  sub h := h.1
  master_mem := ⟨(strictFun V₀ V₁).master_mem, Set.mem_univ f⟩
  inter_mem := by
    rintro W W' ⟨hW, hfW⟩ ⟨hW', hfW'⟩
    exact ⟨strictFun_mem_inter hW hW' ⟨f, Set.mem_inter hfW hfW'⟩, Set.mem_inter hfW hfW'⟩
  up_mem := by rintro W W' ⟨hW, hfW⟩ hW' hWW'; exact ⟨hW', hWW' hfW⟩

end DomainTheory.NeighbourhoodSystems.Exercise510
