/-ai
An infix notation of precedence 70, associating to the left, is introduced for application.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Continuous
public import DomainTheory.DataTypesAsLattices.Graph.funOf

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

infixl:70 " ⬝ " => funOf

end DomainTheory.DataTypesAsLattices
