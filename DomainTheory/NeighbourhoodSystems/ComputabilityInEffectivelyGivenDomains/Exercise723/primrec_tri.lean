/-ai
The triangular-number map, sending k to k times (k + 1) divided by 2, is primitive recursive. The product k times (k + 1) is an exact multiple of 2, so the division is the primitive-recursive division by 2.

Dividing the product of the identity with the successor by 2 is identified with the triangular-number map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)

















































/-- `tri k = k(k+1)/2` is primitive recursive: `tri k * 2 = k(k+1)` is *exact* division by the
literal `2`, computed by `primrec_div2`. -/
theorem primrec_tri : Nat.Primrec tri :=
  (primrec_div2.comp (primrec_mul₂ primrec_id Nat.Primrec.succ)).of_eq fun _ => rfl

end DomainTheory.NeighbourhoodSystems.Exercise723
