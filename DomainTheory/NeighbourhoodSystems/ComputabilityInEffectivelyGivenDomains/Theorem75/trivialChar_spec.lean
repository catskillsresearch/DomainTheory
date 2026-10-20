module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funListOf
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.andFoldl_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.stepFun_funListOf_eq_univ_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.trivStp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.trivialChar

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

theorem trivialChar_spec (eq1 : ℕ → ℕ)
    (heq1 : ∀ s, eq1 s = 1 ↔ P₁.X s.unpair.1 = P₁.X s.unpair.2) (a : ℕ) :
    trivialChar P₁ eq1 a = 1 ↔
      (stepFun (funListOf P₀ P₁ (decodeList a)) : Set (ApproximableMap V₀ V₁)) = Set.univ := by
  rw [stepFun_funListOf_eq_univ_iff P₀ P₁]
  unfold trivialChar
  rw [foldCode_eq']
  have hstep : (fun acc x => trivStp P₁ eq1 (Nat.pair x (Nat.pair acc 0)))
      = (fun acc x => selectFn acc (isOne (eq1 (Nat.pair x.unpair.2 P₁.masterIdx))) 0) := by
    funext acc x
    show trivStp P₁ eq1 (Nat.pair x (Nat.pair acc 0)) = _
    unfold trivStp
    simp only [unpair_pair_fst, unpair_pair_snd]
  rw [hstep, andFoldl_one (fun x => eq1 (Nat.pair x.unpair.2 P₁.masterIdx))]
  refine forall_congr' (fun e => ?_)
  refine imp_congr_right (fun he => ?_)
  rw [heq1]
  simp only [unpair_pair_fst, unpair_pair_snd, P₁.masterIdx_spec]

end DomainTheory.NeighbourhoodSystems
