/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Data.Multiset.MapFold
import all Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpace
public import DomainTheory.InformationSystems.Theorem72
public import DomainTheory.InformationSystems.Factoid25
public import DomainTheory.InformationSystems.Factoid33
public import DomainTheory.InformationSystems.Factoid35
public import DomainTheory.InformationSystems.Factoid75.BoolToken
public import DomainTheory.InformationSystems.Factoid75.BoolPoint
public import DomainTheory.InformationSystems.Factoid75.emptyEntails_mem_botElement
public import DomainTheory.InformationSystems.Factoid75.mem_botElement_emptyEntails
public import DomainTheory.InformationSystems.Factoid75.IsStrict
public import DomainTheory.InformationSystems.Factoid75.IsStrictToken
public import DomainTheory.InformationSystems.Factoid75.BasicInst22

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem IsStrictToken_of_IsStrict (f : ApproximableMap A B) (hf : IsStrict A B f)
    {p : FunToken A B} (hrel : f.rel p.val.1 p.val.2) : IsStrictToken A B p := by
  intro hE
  have hsub : ↑p.val.1 ⊆ A.botElement.carrier := fun x hx =>
    emptyEntails_mem_botElement A (hE x (Finset.mem_coe.1 hx))
  have hout : ↑p.val.2 ⊆ (f.toElement A.botElement).carrier := by
    intro y hy
    refine ⟨p.val.1, hsub, ?_⟩
    have hy' : y ∈ p.val.2 := Finset.mem_coe.1 hy
    exact f.mono hrel (proposition_2_3_iii A p.property.1)
      (fun z hz => by
        have : z = y := Finset.mem_singleton.mp hz
        subst this
        exact B.ent_refl p.property.2 hy')
      p.property.1 (B.con_sing y)
  rw [hf] at hout
  exact fun y hy => mem_botElement_emptyEntails B (hout (Finset.mem_coe.2 hy))

end InfoSys

end DomainTheory.InformationSystems
