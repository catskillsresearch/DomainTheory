/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Fixpoint
public import DomainTheory.InformationSystems.Proposition54
public import DomainTheory.InformationSystems.Proposition55
public import DomainTheory.InformationSystems.Factoid33
public import DomainTheory.InformationSystems.Factoid35
public import DomainTheory.InformationSystems.Proposition74.Basic
public import DomainTheory.InformationSystems.Proposition74.fixChain_toElement_le_fix

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)


theorem toElement_fix_le_fixElement (f : ApproximableMap A A) (g : ApproximableMap B B)
    (h : ApproximableMap A B)
    (hcomm : comp h f = comp g h)
    (hstrict : h.toElement A.botElement = B.botElement) :
    h.toElement (fixElement A f) ≤ fixElement B g := by
  intro Z ⟨u, hu, hrel⟩
  obtain ⟨w, hw, ⟨_, _, v0, hv0, hEnt⟩⟩ :=
    exists_rel_of_subset_image (fixMap A) (approxMap_toElement A A f) u hu
  obtain ⟨n, hn⟩ := hv0
  have hcl := fixChain_toElement_le_fix A B f g h hcomm hstrict hw hn
  have hv0C := fixChain_con A hn
  have hrel' : h.rel v0 {Z} :=
    h.mono hrel hEnt (proposition_2_3_iii B (h.rel_cod hrel)) hv0C (h.rel_cod hrel)
  have hZ : Z ∈ (h.toElement (A.closure v0 hv0C)).carrier :=
    ⟨v0, A.subset_closure hv0C, hrel'⟩
  exact hcl hZ

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
