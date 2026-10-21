/-ai
The element fromCC s contains the singleton of the empty string if and only if s contains the unit neighbourhood of the sum.

Membership under fromCC is the whole token set, the empty-string singleton, or a prefixed copy. The singleton of the empty string is neither the whole token set nor a prefixed copy, so only the unit clause remains. Conversely, that clause records the membership.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Strn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_prependN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.consMapN_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.SigTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tc_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_not_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_not_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tu_not_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tc_not_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_mem_masterSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tu_mem_masterSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumSig_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sinjU_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sinjC_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumMapSig_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tsigObj_sys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tsigMapHom_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Tsig_obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Tsig_map_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_embA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.singleton_nil_ne_univ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.singleton_nil_ne_embA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.CCn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.toCC_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.toCC_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.fromCC

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

@[simp] theorem fromCC_mem_nil {s : (CCn A).Element} :
    (fromCC s).mem ({[]} : Set (Strn A)) ↔ s.mem (jU : Set (SigTok A (Strn A))) := by
  constructor
  · rintro (h0 | ⟨-, hs⟩ | ⟨a', X', hX', heq, hs⟩)
    · exact absurd h0 singleton_nil_ne_univ
    · exact hs
    · exact absurd heq (singleton_nil_ne_embA a' X')
  · intro hs; exact Or.inr (Or.inl ⟨rfl, hs⟩)

end Iso

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
