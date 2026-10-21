/-ai
The numbering num of the two components of a paired natural number is primitive recursive. Explicitly, num n m equals the triangular number of n + m, plus m.

Add the right component to the triangular number of the sum of the two components. That composition is identified with num.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.primrec_tri

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)


/-- `num n m = tri(n+m) + m` is primitive recursive. -/
theorem primrec_num : Nat.Primrec (fun t => num t.unpair.1 t.unpair.2) :=
  (primrec_add₂ (primrec_tri.comp (primrec_add₂ Nat.Primrec.left Nat.Primrec.right))
    Nat.Primrec.right).of_eq fun _ => rfl

end DomainTheory.NeighbourhoodSystems.Exercise723
