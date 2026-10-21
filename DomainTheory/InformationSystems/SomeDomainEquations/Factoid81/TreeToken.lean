/-ai
The tokens of the tree system are given inductively by a bottom token, an atom token carrying an element of the atom type, and left and right pair tokens each carrying a tree token. Decidable equality on these tokens, given decidable equality of the atoms, is introduced by recursion on the two tokens: matching constructors are compared by reflexivity, by equality of the atoms, or by the recursive comparison of the payloads, and tokens built by different constructors are distinct.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false
universe u

/-- Tokens of the tree system: sum tagging of atoms and product left/right copies. -/
inductive TreeToken (α : Type u) where
  | bot : TreeToken α
  | atom : α → TreeToken α
  | pairL : TreeToken α → TreeToken α
  | pairR : TreeToken α → TreeToken α

instance instDecidableEqTreeToken {α : Type u} [DecidableEq α] :
    DecidableEq (TreeToken α)
  | .bot, .bot => isTrue rfl
  | .atom a, .atom b =>
      if h : a = b then isTrue (h ▸ rfl)
      else isFalse fun h' => h (TreeToken.atom.inj h')
  | .pairL a, .pairL b =>
      match instDecidableEqTreeToken a b with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse fun h' => h (TreeToken.pairL.inj h')
  | .pairR a, .pairR b =>
      match instDecidableEqTreeToken a b with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse fun h' => h (TreeToken.pairR.inj h')
  | .bot, .atom _ => isFalse fun h => nomatch h
  | .bot, .pairL _ => isFalse fun h => nomatch h
  | .bot, .pairR _ => isFalse fun h => nomatch h
  | .atom _, .bot => isFalse fun h => nomatch h
  | .atom _, .pairL _ => isFalse fun h => nomatch h
  | .atom _, .pairR _ => isFalse fun h => nomatch h
  | .pairL _, .bot => isFalse fun h => nomatch h
  | .pairL _, .atom _ => isFalse fun h => nomatch h
  | .pairL _, .pairR _ => isFalse fun h => nomatch h
  | .pairR _, .bot => isFalse fun h => nomatch h
  | .pairR _, .atom _ => isFalse fun h => nomatch h
  | .pairR _, .pairL _ => isFalse fun h => nomatch h

end InfoSys
end DomainTheory.InformationSystems
