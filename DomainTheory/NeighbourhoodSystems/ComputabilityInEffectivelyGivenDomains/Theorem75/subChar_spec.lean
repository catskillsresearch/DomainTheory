/-ai
If the step-function neighbourhood of the list decoded from a is nonempty, then the inclusion characteristic of a and b equals 1 if and only if that neighbourhood is contained in the step-function neighbourhood of the list decoded from b.

Nonemptiness makes every conditional output intersection a codomain neighbourhood, so inclusion of step-function neighbourhoods is the family of output inclusions. The characteristic unfolds as a fold whose step selects the codomain inclusion bit of the conditional-intersection index. The fold equals 1 precisely when every decoded entry satisfies that bit, and the inclusion and index specifications turn each bit into the corresponding output inclusion.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funListOf
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interYs_funList_mem_of_nonempty
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.stepFun_funListOf_subset_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interYsIdx
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interYsIdx_spec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.andFoldl_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.subStp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.subChar

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

theorem subChar_spec (incl0 incl1 : ℕ → ℕ)
    (hincl0 : ∀ s, incl0 s = 1 ↔ P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2)
    (hincl1 : ∀ s, incl1 s = 1 ↔ P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2)
    {a : ℕ}
    (hane : (stepFun (funListOf P₀ P₁ (decodeList a)) : Set (ApproximableMap V₀ V₁)).Nonempty)
    (b : ℕ) :
    subChar P₁ incl0 incl1 a b = 1 ↔
      (stepFun (funListOf P₀ P₁ (decodeList a)) : Set (ApproximableMap V₀ V₁)) ⊆
        stepFun (funListOf P₀ P₁ (decodeList b)) := by
  have hcons : ∀ {X : Set α},
      V₀.mem X → V₁.mem (interYs V₁.master (funListOf P₀ P₁ (decodeList a)) X) :=
    fun {X} hX => interYs_funList_mem_of_nonempty P₀ P₁ hane hX
  rw [stepFun_funListOf_subset_iff P₀ P₁ hcons]
  unfold subChar
  rw [foldCode_eq']
  have hstep : (fun acc x => subStp P₁ incl0 incl1 (Nat.pair x (Nat.pair acc a)))
      = (fun acc x => selectFn acc
          (isOne (incl1 (Nat.pair (interYsIdx P₁ incl0 a x.unpair.1) x.unpair.2))) 0) := by
    funext acc x
    show subStp P₁ incl0 incl1 (Nat.pair x (Nat.pair acc a)) = _
    unfold subStp
    simp only [unpair_pair_fst, unpair_pair_snd]
  rw [hstep, andFoldl_one (fun x => incl1 (Nat.pair (interYsIdx P₁ incl0 a x.unpair.1) x.unpair.2))]
  refine forall_congr' (fun e' => ?_)
  refine imp_congr_right (fun he' => ?_)
  rw [hincl1]
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [interYsIdx_spec P₀ P₁ incl0 hincl0 a e'.unpair.1 (hcons (P₀.mem_X e'.unpair.1))]

end DomainTheory.NeighbourhoodSystems
