module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gStep_gamma
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gStep_leaf
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gStep_node
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gEval_pair

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717



variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

















section Computability

variable (fe fU fV : ℕ → ℕ) (mIdx : ℕ)



/-- The output index of `gEval ⟨n, cert⟩` is just `cert`'s first component (all three branches emit
`out`). -/
theorem gEval_out (n cert : ℕ) :
    (gEval fe fU fV mIdx (Nat.pair n cert)).unpair.2 = cert.unpair.1 := by
  rw [gEval_pair]
  rcases nat_shape n with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rw [gStep_gamma, unpair_pair_snd]
  · rw [gStep_leaf, unpair_pair_snd]
  · rw [gStep_node, unpair_pair_snd]

end Computability
end Exercise717
end DomainTheory.NeighbourhoodSystems
