/-ai
Currying the uncurry of a strict map into the strict function space returns the original map.

Extensionality of strict maps and of approximable maps reduces the claim to relations. A curried relation presents its codomain as a step-function set of a list, and the generation lemma with the section computation of the uncurry turns section membership in each step into the corresponding relation of the original map. Conversely, a relation of the original map supplies the neighbourhood data, and the same two lemmas put the section into every step of the list.
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
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.toStrictMap_rel
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_toStrictFilter
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.rel_sstepFun_iff
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashCurryMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashUncurryMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.section_uncurry_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

/-- **Roundtrip (ii): `curry⊥ ∘ uncurry⊥ = id`.** -/
theorem smashCurry_uncurry (h : StrictMap V₀ (strictFun V₁ V₂)) :
    smashCurryMap (smashUncurryMap h) = h := by
  apply Subtype.ext
  apply ApproximableMap.ext
  intro X N
  constructor
  · rintro ⟨hX, hN, hmem⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hN
    refine (rel_sstepFun_iff h.1 hX hL).mpr (fun p hp => ?_)
    exact (section_uncurry_rel h hX (hL p hp).1).mp (hmem p hp)
  · intro hrel
    have hX : V₀.mem X := h.1.rel_dom hrel
    have hN : (strictFun V₁ V₂).mem N := h.1.rel_cod hrel
    refine ⟨hX, hN, ?_⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hN
    intro p hp
    exact (section_uncurry_rel h hX (hL p hp).1).mpr
      ((rel_sstepFun_iff h.1 hX hL).mp hrel p hp)

end DomainTheory.NeighbourhoodSystems.Exercise510
