/-ai
Two elements are equal when their carriers are equal.

The proof matches the two element structures and substitutes the equality of the carriers.

The carrier of an element is included in itself.

This is reflexivity of inclusion.

Inclusion of carriers is transitive.

This is transitivity of inclusion.

If each of two elements contains the carrier of the other, the elements are equal.

Antisymmetry of inclusion equates the carriers, and extensionality of elements equates the elements.

This instance orders elements by inclusion of their carriers, with the three preceding facts as reflexivity, transitivity, and antisymmetry. That inclusion is Scott's ordering of the domain determined by the information system.
ai-/
module

public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Basic
import all Mathlib.Data.Set.Basic
public import DomainTheory.InformationSystems.InformationSystems.InfoSys.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.InfoSys.Element

@[expose] public section

/-!
# Scott Information Systems

Following Dana Scott, *"Domains for Denotational Semantics"* (ICALP 1982) and the
compact presentation in Glynn Winskel, *The Formal Semantics of Programming
Languages*, Chapter 8.

Following Scott's **Definition 2.1**, an information system is a structure
`(P, Δ, Con, ⊢)` where

* `P` is a set of *data objects* / *propositions* (our token type `α`);
* `Δ ∈ P` is a distinguished *least informative* object (here the field `bot`);
* `Con` is a set of finite subsets of `P`, the *consistent* sets; and
* `⊢` (entailment, here `Ent`) relates a finite set to a token it forces.

Scott's six axioms (Def. 2.1) are, for finite `u, v ⊆ P` and `X ∈ P`:

* (i)   `u ∈ Con` whenever `u ⊆ v ∈ Con`              — `con_subset`
* (ii)  `{X} ∈ Con`                                    — `con_sing`
* (iii) `u ∪ {X} ∈ Con` whenever `u ⊢ X`               — `ent_con`
* (iv)  `u ⊢ Δ`                                         — `ent_bot`
* (v)   `u ⊢ X` whenever `X ∈ u`                        — `ent_refl`
* (vi)  if `v ⊢ Y` for all `Y ∈ u` and `u ⊢ X` then `v ⊢ X` — `ent_trans`

The **domain** determined by an information system is the poset of its *elements*
(a.k.a. *ideals*): sets of tokens that are consistent on every finite subset and
closed under entailment, ordered by inclusion. This file sets up the structure, the
notion of element, and the partial order; later files build the function, product,
and sum spaces.

This is the **1982** presentation; the development is kept choice-free (constructive),
matching Scott's emphasis on the constructive nature of the definitions.
-/

namespace DomainTheory.InformationSystems

universe u


namespace InfoSys

variable {α : Type u} [DecidableEq α] (sys : InfoSys α)


/-- Extensional equality of elements. -/
theorem Element.ext {x y : sys.Element} (h : x.carrier = y.carrier) : x = y := by
  cases x
  cases y
  subst h
  rfl

/-- Reflexivity of the carrier-inclusion order. -/
theorem element_le_refl (x : sys.Element) : x.carrier ⊆ x.carrier :=
  Set.Subset.refl _

/-- Transitivity of the carrier-inclusion order. -/
theorem element_le_trans (x y z : sys.Element)
    (hxy : x.carrier ⊆ y.carrier) (hyz : y.carrier ⊆ z.carrier) :
    x.carrier ⊆ z.carrier :=
  Set.Subset.trans hxy hyz

/-- Antisymmetry of the carrier-inclusion order. -/
theorem element_le_antisymm (x y : sys.Element)
    (hxy : x.carrier ⊆ y.carrier) (hyx : y.carrier ⊆ x.carrier) :
    x = y :=
  Element.ext sys (Set.Subset.antisymm hxy hyx)

/-- Elements are ordered by inclusion of their carriers; this is the Scott ordering. -/
instance instPartialOrderElement : PartialOrder sys.Element where
  le x y := x.carrier ⊆ y.carrier
  le_refl := element_le_refl sys
  le_trans := element_le_trans sys
  le_antisymm := element_le_antisymm sys
end InfoSys
end DomainTheory.InformationSystems
