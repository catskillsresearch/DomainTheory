module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.encodeDeltaPair

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union_mem_or_empty
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

theorem encodeDeltaPair_lt (δ : ℕ → Bool × Bool) : ∀ n, encodeDeltaPair δ n < 4 ^ n
  | 0 => by simp [encodeDeltaPair]
  | n + 1 => by
      have ih := encodeDeltaPair_lt δ n
      have h4 : (4 : ℕ) ^ (n + 1) = 4 ^ n * 4 := pow_succ 4 n
      show encodeDeltaPair δ n +
        ((if (δ n).1 then 1 else 0) + (if (δ n).2 then 2 else 0)) * 4 ^ n < 4 ^ (n + 1)
      rcases Bool.eq_false_or_eq_true (δ n).1 with h1 | h1 <;>
        rcases Bool.eq_false_or_eq_true (δ n).2 with h2 | h2 <;>
        simp only [h1, h2, ite_true, ite_false, Bool.false_eq_true] <;> omega

end DomainTheory.NeighbourhoodSystems
