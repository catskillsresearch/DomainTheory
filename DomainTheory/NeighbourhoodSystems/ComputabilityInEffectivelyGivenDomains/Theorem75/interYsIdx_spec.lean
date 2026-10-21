/-ai
When the conditional output intersection of the list decoded from a against the domain neighbourhood at k is a codomain neighbourhood, the neighbourhood at interYsIdx of a and k equals that intersection.

Unfold the index and rewrite the fold as a list fold. The packed step equals conditional intersection on the unpacked entry, by the selection law for isOne. Rewrite the conditional output intersection as the conditional set, and apply the specification of the conditional fold at the master index.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.selectFn_isOne
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.condSet_eq_interYs
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interYsStp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interYsIdx
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.condFoldl_spec

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

/-- **`interYsIdx` indexes `interYs Δ₁ (funListOf (decodeList a)) (X₀_k)`** (when that is consistent,
which it is whenever `stepFun (funListOf (decodeList a))` is non-empty). Choice-free. -/
theorem interYsIdx_spec (incl0 : ℕ → ℕ)
    (hincl0 : ∀ s, incl0 s = 1 ↔ P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) (a k : ℕ)
    (hcons : V₁.mem (interYs V₁.master (funListOf P₀ P₁ (decodeList a)) (P₀.X k))) :
    P₁.X (interYsIdx P₁ incl0 a k)
      = interYs V₁.master (funListOf P₀ P₁ (decodeList a)) (P₀.X k) := by
  unfold interYsIdx
  rw [foldCode_eq']
  have hstep : (fun acc x => interYsStp P₁ incl0 (Nat.pair x (Nat.pair acc k)))
      = (fun acc x => if incl0 (Nat.pair k x.unpair.1) = 1
            then P₁.inter acc x.unpair.2 else acc) := by
    funext acc x
    show interYsStp P₁ incl0 (Nat.pair x (Nat.pair acc k)) = _
    unfold interYsStp
    simp only [unpair_pair_fst, unpair_pair_snd]
    exact selectFn_isOne _ _ _
  rw [hstep]
  rw [← condSet_eq_interYs P₀ P₁ k (decodeList a)] at hcons ⊢
  exact condFoldl_spec P₀ P₁ incl0 hincl0 k (decodeList a) V₁.master P₁.masterIdx
    P₁.masterIdx_spec V₁.master_mem hcons

end DomainTheory.NeighbourhoodSystems
