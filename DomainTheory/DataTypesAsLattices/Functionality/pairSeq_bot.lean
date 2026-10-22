
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
