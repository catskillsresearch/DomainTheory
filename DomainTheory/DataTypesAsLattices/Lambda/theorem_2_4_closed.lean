/-ai
Every term, interpreted in the constantly bottom environment, denotes a combinatory element.

The completeness form of the combinator theorem rewrites the interpretation as the value of the erased combinator. The combinatory lemma for erased combinators reduces the claim to combinatory status of every variable value, and each of those values is bottom. Bottom equals the application of the predecessor combinator to the zero combinator, by the predecessor application law and equation (2.6), and that application of two combinatory constants is combinatory.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_6
public import DomainTheory.DataTypesAsLattices.Lambda.predC_app
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_4_complete
public import DomainTheory.DataTypesAsLattices.Lambda.ofComb_combinatory

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem theorem_2_4_closed (t : Term) :
    IsCombinatory (interp t (fun _ => botElem)) := by
  rw [theorem_2_4_complete]
  refine ofComb_combinatory _ _ fun _ => ?_
  have hbot : funOf predC zeroC = botElem := by
    rw [predC_app]; exact eq_2_6
  exact hbot ▸ IsCombinatory.app IsCombinatory.pred IsCombinatory.zero

end DomainTheory.DataTypesAsLattices
