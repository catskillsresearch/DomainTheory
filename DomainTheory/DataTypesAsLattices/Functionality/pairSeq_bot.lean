/-ai
The sequence pair of bottom with bottom is bottom.

Function and set extensionality, together with the definitions of the conditional set and of bottom, show that the body of the two-place sequence is the constant function with value bottom. Unfolding sequence pairing, the graph of that constant function is bottom.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















theorem pairSeq_bot : pairSeq botElem botElem = botElem := by
  have hbody : (fun z => condSet z botElem (condSet (predSet z) botElem botElem)) =
      fun _ => botElem := by
    funext z
    ext n
    simp [condSet, botElem]
  simpa [pairSeq, seq2, hbody] using graph_const_bot

end DomainTheory.DataTypesAsLattices
