/-ai
Uncurrying the curry of a strict map out of the smash returns the original map.

Extensionality of strict maps and of approximable maps reduces the claim to relations. If the composite relates a smash neighbourhood to an output and the neighbourhood is the master, the preimages are the masters, strictness of the section forces the output to be the master, and the original map relates the master to the master. If the neighbourhood is a proper product, the computation for principal smash pairs recovers the original relation. Conversely, the domain of a relation is a smash neighbourhood. On the master, strictness of the original map makes the output the master, and the curry relates the first master to the step of the second master. On a proper product, the section at the first factor relates the second factor to the output, and that strict section witnesses that the step is a neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_proper
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
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.toStrictMap_rel
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_toStrictFilter
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashPair_principal_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashSection
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.isStrict_smashSection
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashCurryMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashUncurryMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

/-- **Roundtrip (i): `uncurry⊥ ∘ curry⊥ = id`.** -/
theorem smashUncurry_curry (g : StrictMap (smash V₀ V₁) V₂) :
    smashUncurryMap (smashCurryMap g) = g := by
  apply Subtype.ext
  apply ApproximableMap.ext
  intro W Z
  constructor
  · rintro ⟨hW, hcurry⟩
    rcases hW with rfl | ⟨X, Y, hXp, hXne, hYp, hYne, rfl⟩
    · simp only [inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hcurry
      obtain ⟨hXm, _, hsec⟩ := hcurry
      have hZ : Z = V₂.master := isStrict_smashSection g.2 hXm hsec
      rw [hZ]; exact g.1.master_rel
    · simp only [inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hcurry
      obtain ⟨hX, _, hY, hmem⟩ := hcurry
      exact (smashPair_principal_apply g.1 hXp hXne hYp hYne).mp hmem
  · intro hrel
    have hW : (smash V₀ V₁).mem W := g.1.rel_dom hrel
    rcases hW with rfl | ⟨X, Y, hXp, hXne, hYp, hYne, rfl⟩
    · have hZ : Z = V₂.master := g.2 hrel
      subst hZ
      refine ⟨Or.inl rfl, ?_⟩
      simp only [inl_preimage_prodNbhd, inr_preimage_prodNbhd, sstep_master_eq]
      exact ⟨V₀.master_mem, (strictFun V₁ V₂).master_mem, Set.mem_univ _⟩
    · refine ⟨smash_mem_proper hXp hXne hYp hYne, ?_⟩
      simp only [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
      have hsec : (smashSection g.1 hXp).rel Y Z :=
        ⟨hYp, (smashPair_principal_apply g.1 hXp hXne hYp hYne).mpr hrel⟩
      exact ⟨hXp, sstep_mem_of_mem
        (g := ⟨smashSection g.1 hXp, isStrict_smashSection g.2 hXp⟩) hsec, hsec⟩

end DomainTheory.NeighbourhoodSystems.Exercise510
