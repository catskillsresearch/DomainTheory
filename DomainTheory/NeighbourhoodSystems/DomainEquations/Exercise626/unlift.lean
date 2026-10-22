module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTok_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTok_mem_embF_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.mem_liftBot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.mem_liftUp

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

/-- The **unlift** of an element that lies above the fresh bottom (i.e. contains `0Δ`): the
`𝒟`-element `{X ∣ 0X ∈ z}`. -/
def unlift (z : (liftTok D hD).Element) (hz : z.mem (embBit false D.master)) : D.Element where
  mem X := z.mem (embBit false X)
  sub := fun hX => liftTok_mem_embF_inv (z.sub hX)
  master_mem := hz
  inter_mem := by
    intro X X' hX hX'
    have hz' := z.inter_mem hX hX'
    rwa [embBit_inter] at hz'
  up_mem := by
    intro X Y hX hY hXY
    exact z.up_mem hX (liftTok_mem_embF hY) (embBit_subset.mpr hXY)

end Exercise619

end DomainTheory.NeighbourhoodSystems
