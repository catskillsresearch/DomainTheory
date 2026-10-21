/-ai
The joint condition that the extracted value equals a proposed value and that every index of the decoded extracted list is a set bit of a proposed word is recursively decidable. The word is packed as the code, then the proposed value, then the bit word.

Conjoin the decidable equality of the primitive-recursive extracted value of the first component with the first component of the second component, and the decidable list bit test.
ai-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.primrec_untagVal
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.untagList_bitAt_isComputable

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)



































































/-- **`(c, j, m) ↦ untagVal c = j ∧ ∀i ∈ decodeList (untagList c), m.testBit i`.** Recursively
decidable, packed `(c,(j,m))`-style. -/
theorem untagVal_and_isComputable :
    RecDecidable (fun w : ℕ => untagVal w.unpair.1 = w.unpair.2.unpair.1 ∧
      ∀ i ∈ decodeList (untagList w.unpair.1), bitAt w.unpair.2.unpair.2 i = 1) :=
  (RecDecidable.natEq (primrec_untagVal.comp Nat.Primrec.left)
    (Nat.Primrec.left.comp Nat.Primrec.right)).and untagList_bitAt_isComputable

end DomainTheory.NeighbourhoodSystems.Exercise723
