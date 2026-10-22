module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.listGet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.eqB
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.consB
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.intI
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.eqB_packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.consB_packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.intI_packT

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

variable (fcons feq finter : ℕ → ℕ)

/-- **The `D^§` decider step.** `p = pair (pair i j) tbl`. Returns `packT eqBit consBit interIdx`,
case-splitting on `i = 0` / `j = 0` (the `Γ` identity), then on parities (leaf `2a+1` vs node
`2a+2`). Leaf∩leaf delegates to `D`'s deciders; node∩node ANDs/combines the two children read from
the memo table `tbl`. -/
def dsharpStep (p : ℕ) : ℕ :=
  let i := p.unpair.1.unpair.1
  let j := p.unpair.1.unpair.2
  let tbl := p.unpair.2
  let w := p.unpair.1
  let na := i / 2 - 1
  let nb := j / 2 - 1
  let r1 := listGet tbl (w - 1 - Nat.pair na.unpair.1 nb.unpair.1)
  let r2 := listGet tbl (w - 1 - Nat.pair na.unpair.2 nb.unpair.2)
  selectFn (1 - i) (packT (1 - j) 1 j)
    (selectFn (1 - j) (packT (1 - i) 1 i)
      (selectFn (i % 2)
        (selectFn (j % 2)
          (packT (feq (Nat.pair (i / 2) (j / 2))) (fcons (Nat.pair (i / 2) (j / 2)))
            (2 * finter (Nat.pair (i / 2) (j / 2)) + 1))
          (packT 0 0 0))
        (selectFn (j % 2) (packT 0 0 0)
          (packT (eqB r1 * eqB r2) (consB r1 * consB r2)
            (2 * Nat.pair (intI r1) (intI r2) + 2)))))

end Proposition77

end DomainTheory.NeighbourhoodSystems
