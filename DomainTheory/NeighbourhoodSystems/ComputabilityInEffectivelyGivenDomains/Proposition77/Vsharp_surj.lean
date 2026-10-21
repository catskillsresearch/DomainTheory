/-ai
Every neighbourhood of the section domain equals the enumerated set at some index.

Induct on the neighbourhood. The master neighbourhood is the value at 0. A zero embedding of a neighbourhood of the underlying domain is the value at 2n+1, where n is a code of that neighbourhood. A paired embedding of two neighbourhoods is the value at two times the pair of their codes, plus two: the even clause and the unpairing of a pair recover those codes.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_odd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_even

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- Every neighbourhood of `D^§` is enumerated as some `V k` (surjectivity of `V`). -/
theorem Vsharp_surj {W : Set (List Bool × α)} (hW : MemS D W) : ∃ k, Vsharp D P k = W := by
  induction hW with
  | gamma => exact ⟨0, Vsharp_zero P⟩
  | @zero X hX => obtain ⟨n, hn⟩ := P.surj hX; exact ⟨2 * n + 1, by rw [Vsharp_odd, hn]⟩
  | @pair Pp Qq _ _ ihP ihQ =>
      obtain ⟨a, ha⟩ := ihP
      obtain ⟨b, hb⟩ := ihQ
      refine ⟨2 * Nat.pair a b + 2, ?_⟩
      have h1 : (Nat.pair a b).unpair.1 = a := by rw [unpair_pair]
      have h2 : (Nat.pair a b).unpair.2 = b := by rw [unpair_pair]
      rw [Vsharp_even, h1, h2, ha, hb]

end Proposition77

end DomainTheory.NeighbourhoodSystems
