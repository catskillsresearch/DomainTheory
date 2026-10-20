/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module


public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35

@[expose] public section

universe u v

namespace DomainTheory.InformationSystems
namespace InfoSys

open DomainTheory.InformationSystems.Constructive

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

/-- **Definition 5.1 (Scott 1982).** Approximable mapping between information systems. -/
structure ApproximableMap (A : InfoSys α) (B : InfoSys β) where
  rel : Finset α → Finset β → Prop
  rel_dom : ∀ {u v}, rel u v → u ∈ A.Con
  rel_cod : ∀ {u v}, rel u v → v ∈ B.Con
  empty_rel : rel ∅ ∅
  union_right : ∀ {u v v'}, rel u v → rel u v' → rel u (v ∪' v')
  mono : ∀ {u u' v v'},
    rel u v → A.EntSet u' u → B.EntSet v v' → u' ∈ A.Con → v' ∈ B.Con → rel u' v'

end InfoSys
end DomainTheory.InformationSystems
