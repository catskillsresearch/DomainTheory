
module

public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq
public import DomainTheory.DataTypesAsLattices.Retracts.graph_const_bot
public import DomainTheory.DataTypesAsLattices.Lambda.seq2
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.predSet
public import DomainTheory.DataTypesAsLattices.Pomega.e

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
