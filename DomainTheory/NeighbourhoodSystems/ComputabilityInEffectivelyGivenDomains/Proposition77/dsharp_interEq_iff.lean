/-ai
The sharp neighbourhoods of n and m are equal to the sharp neighbourhood of k exactly when the product of the consistency bit at the pair of n and m with the equality bit comparing the computed intersection index to k is one.

A product of naturals is one exactly when both factors are one. The decider specification supplies consistency and intersection correctness at n and m, and equality at the computed intersection index against k. If the neighbourhoods agree, k witnesses consistency and the computed intersection equals the neighbourhood of k. Conversely, consistency makes the computed intersection equal the meet, and equality with the neighbourhood of k gives the claim.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.gOf
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.eqB
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.consB
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.intI
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.eqB_packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.consB_packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.intI_packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharpStep
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharp_decider_spec

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

variable (fcons feq finter : ℕ → ℕ)

/-- **Decidability of `7.1(i)` for `D^§`.** `Vₙ ∩ Vₘ = V_k` iff `(n,m)` is consistent and the
computed intersection index agrees with `k` under `D^§`-equality. Inconsistency forces the product
to `0` (and then `Vₙ ∩ Vₘ = ∅ ≠ V_k`, since `V_k` is nonempty), so the single product decider is
correct on the nose. -/
theorem dsharp_interEq_iff (hD : ∀ X, D.mem X → X.Nonempty)
    (hcons : ∀ a b, fcons (Nat.pair a b) = 1 ↔ ∃ l, P.X l ⊆ P.X a ∩ P.X b)
    (heq : ∀ a b, feq (Nat.pair a b) = 1 ↔ P.X a = P.X b)
    (hinter : ∀ a b, (∃ l, P.X l ⊆ P.X a ∩ P.X b) → P.X (finter (Nat.pair a b)) = P.X a ∩ P.X b)
    (n m k : ℕ) :
    (Vsharp D P n ∩ Vsharp D P m = Vsharp D P k) ↔
      consB (gOf (dsharpStep fcons feq finter) (Nat.pair n m))
        * eqB (gOf (dsharpStep fcons feq finter)
            (Nat.pair (intI (gOf (dsharpStep fcons feq finter) (Nat.pair n m))) k)) = 1 := by
  obtain ⟨hc0, hi0, _⟩ := dsharp_decider_spec P fcons feq finter hD hcons heq hinter n m
  obtain ⟨_, _, he⟩ := dsharp_decider_spec P fcons feq finter hD hcons heq hinter
    (intI (gOf (dsharpStep fcons feq finter) (Nat.pair n m))) k
  rw [nat_mul_eq_one]
  constructor
  · intro hEq
    have hch : ∃ l, Vsharp D P l ⊆ Vsharp D P n ∩ Vsharp D P m := ⟨k, hEq.ge⟩
    exact ⟨hc0.mpr hch, he.mpr ((hi0 hch).trans hEq)⟩
  · rintro ⟨hcb, heb⟩
    rw [← hi0 (hc0.mp hcb)]; exact he.mp heb

end Proposition77

end DomainTheory.NeighbourhoodSystems
