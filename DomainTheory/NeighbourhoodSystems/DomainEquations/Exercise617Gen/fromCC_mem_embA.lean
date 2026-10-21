/-ai
The element fromCC s contains the letter-prefixed copy of a neighbourhood X of the string system if and only if s contains the tagged copy of that letter and of X.

Membership under fromCC is the whole token set, the singleton of the empty string, or some prefixed copy. The prefixed copy is neither the whole token set nor the empty-string singleton. If it equals another prefixed copy, the letter and the set agree because X is nonempty, so the tagged membership is the required one. Conversely, the prefixed-copy clause of the definition records that tagged membership.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Strn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_prependN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.consMapN_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jc
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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.embA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_embA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.embA_ne_univ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.singleton_nil_ne_embA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.CCn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.toCC_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.toCC_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.embA_eq_embA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.fromCC
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.fromCC_mem_nil

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

omit [Inhabited A] in

@[simp] theorem fromCC_mem_embA {s : (CCn A).Element} {a : A} {X : Set (Strn A)} (hX : (Cn A).mem X) :
    (fromCC s).mem (embA a X) ↔ s.mem (jc a X) := by
  constructor
  · rintro (h0 | ⟨heq, hs⟩ | ⟨a', X', hX', heqj, hs⟩)
    · exact absurd h0 (embA_ne_univ a X)
    · exact absurd heq.symm (singleton_nil_ne_embA a X)
    · obtain ⟨rfl, rfl⟩ := embA_eq_embA (Cn_nonempty X hX) heqj
      exact hs
  · intro hs; exact Or.inr (Or.inr ⟨a, X, hX, rfl, hs⟩)

end Iso

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
