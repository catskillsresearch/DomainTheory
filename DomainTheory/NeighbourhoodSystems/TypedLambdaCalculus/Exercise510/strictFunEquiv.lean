/-ai
The elements of the strict function space are order-isomorphic to the strict approximable maps, sending a filter to the strict map it represents and a strict map to the filter of neighbourhoods that contain it. A neighbourhood of the represented map is a step-function set in the filter, and the generation lemma matches the whole set with its individual steps; a neighbourhood of the filter belongs to the strict function space, and each of its steps belongs to the filter. A relation of the represented filter is membership of the corresponding step, and a relation of the map makes that step a neighbourhood containing the map. If the represented map of one filter lies below that of another, each step in a neighbourhood of the first filter is a relation of the second map and hence belongs to the second filter; an inequality of filters sends each relation of the first represented map to the second.
ai-/
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
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep_mem_of_mem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstepFun_iff
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.toStrictMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.toStrictMap_rel
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.toStrictFilter
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_toStrictFilter

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Exercise 5.10 — the strict function space is complete.** `|𝒟₀ →⊥ 𝒟₁|` is order-isomorphic to
the strict approximable maps `𝒟₀ → 𝒟₁`. -/
def strictFunEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    (strictFun V₀ V₁).Element ≃o StrictMap V₀ V₁ where
  toFun := toStrictMap
  invFun := toStrictFilter
  left_inv φ := by
    apply Element.ext
    intro W
    constructor
    · rintro ⟨hWmem, hfW⟩
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := hWmem
      exact (mem_sstepFun_iff φ hL).mpr (fun p hp => hfW p hp)
    · intro hW
      refine ⟨φ.sub hW, ?_⟩
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := φ.sub hW
      intro p hp
      exact (mem_sstepFun_iff φ hL).mp hW p hp
  right_inv f := by
    apply Subtype.ext
    apply ApproximableMap.ext
    intro X Y
    constructor
    · rintro ⟨_, hf⟩; exact hf
    · intro hf; exact ⟨sstep_mem_of_mem (g := f) hf, hf⟩
  map_rel_iff' := by
    intro φ φ'
    constructor
    · intro h W hW
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := φ.sub hW
      refine (mem_sstepFun_iff φ' hL).mpr (fun p hp => ?_)
      exact h p.1 p.2 ((mem_sstepFun_iff φ hL).mp hW p hp)
    · intro h X Y hrel
      exact h _ hrel

end DomainTheory.NeighbourhoodSystems.Exercise510
